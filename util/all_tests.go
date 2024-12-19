// Copyright (c) 2015, Google Inc.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

//go:build ignore

package main

import (
	"bytes"
	"context"
	"errors"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"boringssl.googlesource.com/boringssl/util/testconfig"
	"boringssl.googlesource.com/boringssl/util/testresult"
)

// TODO(davidben): Link tests with the malloc shim and port -malloc-test to this runner.

var (
	useValgrind     = flag.Bool("valgrind", false, "If true, run code under valgrind")
	valgrindSuppDir = flag.String("valgrind-supp-dir", ".", "The directory where Valgrind suppression files can be found.")
	useCallgrind    = flag.Bool("callgrind", false, "If true, run code under valgrind to generate callgrind traces.")
	useGDB          = flag.Bool("gdb", false, "If true, run BoringSSL code under gdb")
	useSDE          = flag.Bool("sde", false, "If true, run BoringSSL code under Intel's SDE for each supported chip")
	sslTests        = flag.Bool("ssl-tests", true, "If true, run BoringSSL tests against libssl")
	sdePath         = flag.String("sde-path", "sde", "The path to find the sde binary.")
	buildDir        = flag.String("build-dir", "build", "The build directory to run the tests from.")
	numWorkers      = flag.Int("num-workers", runtime.NumCPU(), "Runs the given number of workers when testing.")
	jsonOutput      = flag.String("json-output", "", "The file to output JSON results to.")
	mallocTest      = flag.Int64("malloc-test", -1, "If non-negative, run each test with each malloc in turn failing from the given number onwards.")
	mallocTestDebug = flag.Bool("malloc-test-debug", false, "If true, ask each test to abort rather than fail a malloc. This can be used with a specific value for --malloc-test to identity the malloc failing that is causing problems.")
)

type test struct {
	testconfig.Test

	shard, numShards int
	// cpu, if not empty, contains a code to simulate. For SDE, run `sde64
	// -help` to get a list of these codes. For ARM, see gtest_main.cc for
	// the supported values.
	cpu string
}

type result struct {
	Test   test
	Passed bool
	Error  error
}

// sdeCPUs contains a list of CPU code that we run all tests under when *useSDE
// is true.
var sdeCPUs = []string{

	"p4p", // Pentium4 Prescott
	"mrm", // Merom
	"pnr", // Penryn
	"nhm", // Nehalem
	"wsm", // Westmere
	"snb", // Sandy Bridge
	"ivb", // Ivy Bridge
	"hsw", // Haswell
	"bdw", // Broadwell
	"slt", // Saltwell
	"slm", // Silvermont
	"glm", // Goldmont
	"glp", // Goldmont Plus
	"tnt", // Tremont
	"skl", // Skylake
	"cnl", // Cannon Lake
	"icl", // Ice Lake
	"skx", // Skylake server
	"clx", // Cascade Lake
	"cpx", // Cooper Lake
	"icx", // Ice Lake server
	"tgl", // Tiger Lake
}

func targetArchMatchesRuntime(target string) bool {
	if (target == "") ||
		(target == "x86" && runtime.GOARCH == "amd64") ||
		(target == "arm" && (runtime.GOARCH == "arm" || runtime.GOARCH == "arm64")) {
		return true
	}
	return false
}

func valgrindOf(ctx context.Context, dbAttach bool, supps []string, path string, args ...string) (context.Context, *exec.Cmd) {
	valgrindArgs := []string{"--error-exitcode=99", "--track-origins=yes", "--leak-check=full", "--trace-children=yes", "--quiet"}
	for _, supp := range supps {
		valgrindArgs = append(valgrindArgs, "--suppressions="+*valgrindSuppDir+"/"+supp)
	}
	if dbAttach {
		valgrindArgs = append(valgrindArgs, "--db-attach=yes", "--db-command=xterm -e gdb -nw %f %p")
	}
	valgrindArgs = append(valgrindArgs, path)
	valgrindArgs = append(valgrindArgs, args...)

	return ctx, exec.CommandContext(ctx, "valgrind", valgrindArgs...)
}

func callgrindOf(ctx context.Context, path string, args ...string) (context.Context, *exec.Cmd) {
	valgrindArgs := []string{"-q", "--tool=callgrind", "--dump-instr=yes", "--collect-jumps=yes", "--callgrind-out-file=" + *buildDir + "/callgrind/callgrind.out.%p"}
	valgrindArgs = append(valgrindArgs, path)
	valgrindArgs = append(valgrindArgs, args...)

	return ctx, exec.CommandContext(ctx, "valgrind", valgrindArgs...)
}

func gdbOf(ctx context.Context, path string, args ...string) (context.Context, *exec.Cmd) {
	xtermArgs := []string{"-e", "gdb", "--args"}
	xtermArgs = append(xtermArgs, path)
	xtermArgs = append(xtermArgs, args...)

	return ctx, exec.CommandContext(ctx, "xterm", xtermArgs...)
}

func sdeOf(ctx context.Context, cpu, path string, args ...string) (context.Context, context.CancelFunc, *exec.Cmd) {
	sdeArgs := []string{"-" + cpu}
	// The kernel's vdso code for gettimeofday sometimes uses the RDTSCP
	// instruction. Although SDE has a -chip_check_vsyscall flag that
	// excludes such code by default, it does not seem to work. Instead,
	// pass the -chip_check_exe_only flag which retains test coverage when
	// statically linked and excludes the vdso.
	if cpu == "p4p" || cpu == "pnr" || cpu == "mrm" || cpu == "slt" {
		sdeArgs = append(sdeArgs, "-chip_check_exe_only")
	}
	sdeArgs = append(sdeArgs, "--", path)
	sdeArgs = append(sdeArgs, args...)

	// TODO(CryptoAlg-2154):SDE+ASAN tests will hang without exiting if tests pass for an unknown reason.
	// Current workaround is to manually cancel the run after 20 minutes and check the output.
	ctx, cancel := context.WithTimeout(ctx, 1800*time.Second)

	return ctx, cancel, exec.CommandContext(ctx, *sdePath, sdeArgs...)
}

var (
	errMoreMallocs = errors.New("child process did not exhaust all allocation calls")
	errTestSkipped = errors.New("test was skipped")
	errTestHanging = errors.New("test hangs without exiting")
)

func runTestOnce(test test, mallocNumToFail int64) (passed bool, err error) {
	prog := filepath.Join(*buildDir, test.Cmd[0])
	args := append([]string{}, test.Cmd[1:]...)
	if *useSDE {
		// SDE is neither compatible with the unwind tester nor automatically
		// detected.
		args = append(args, "--no_unwind_tests")
	}
	var cmd *exec.Cmd
	var cancel context.CancelFunc

	ctx := context.Background()

	if *useValgrind {
		ctx, cmd = valgrindOf(ctx, false, test.ValgrindSupp, prog, args...)
	} else if *useCallgrind {
		ctx, cmd = callgrindOf(ctx, prog, args...)
	} else if *useGDB {
		ctx, cmd = gdbOf(ctx, prog, args...)
	} else if *useSDE {
		ctx, cancel, cmd = sdeOf(ctx, test.cpu, prog, args...)
		defer cancel()
	} else {
		cmd = exec.CommandContext(ctx, prog, args...)
	}
	if test.Env != nil || test.numShards != 0 {
		cmd.Env = make([]string, len(os.Environ()))
		copy(cmd.Env, os.Environ())
	}
	if test.Env != nil {
		cmd.Env = append(cmd.Env, test.Env...)
	}
	if test.numShards != 0 {
		cmd.Env = append(cmd.Env, fmt.Sprintf("GTEST_SHARD_INDEX=%d", test.shard))
		cmd.Env = append(cmd.Env, fmt.Sprintf("GTEST_TOTAL_SHARDS=%d", test.numShards))
	}
	var outBuf bytes.Buffer
	cmd.Stdout = &outBuf
	cmd.Stderr = &outBuf
	if mallocNumToFail >= 0 {
		cmd.Env = os.Environ()
		cmd.Env = append(cmd.Env, "MALLOC_NUMBER_TO_FAIL="+strconv.FormatInt(mallocNumToFail, 10))
		if *mallocTestDebug {
			cmd.Env = append(cmd.Env, "MALLOC_ABORT_ON_FAIL=1")
		}
		cmd.Env = append(cmd.Env, "_MALLOC_CHECK=1")
	}

	if err := cmd.Start(); err != nil {
		return false, err
	}

	if err := cmd.Wait(); err != nil {
		var exitError *exec.ExitError
		if errors.As(err, &exitError) {
			switch exitError.Sys().(syscall.WaitStatus).ExitStatus() {
			case 88:
				return false, errMoreMallocs
			case 89:
				fmt.Print(string(outBuf.Bytes()))
				return false, errTestSkipped
			}
			select {
			case <-ctx.Done():
				if errors.Is(ctx.Err(), context.DeadlineExceeded) {
					return testPass(outBuf), errTestHanging
				} else if ctx.Err() != nil {
					return false, ctx.Err()
				}
			default:
				// Nothing
			}
		}
		fmt.Print(string(outBuf.Bytes()))
		return false, err
	}

	return testPass(outBuf), nil
}

func testPass(outBuf bytes.Buffer) bool {
	// Account for Windows line-endings.
	stdout := bytes.Replace(outBuf.Bytes(), []byte("\r\n"), []byte("\n"), -1)

	if bytes.HasSuffix(stdout, []byte("PASS\n")) &&
		(len(stdout) == 5 || stdout[len(stdout)-6] == '\n') {
		return true
	}

	// Also accept a googletest-style pass line. This is left here in
	// transition until the tests are all converted and this script made
	// unnecessary.
	if bytes.Contains(stdout, []byte("\n[  PASSED  ]")) {
		return true
	}

	fmt.Print(string(outBuf.Bytes()))
	return false
}

func runTest(test test) (bool, error) {
	if *mallocTest < 0 {
		return runTestOnce(test, -1)
	}

	for mallocNumToFail := int64(*mallocTest); ; mallocNumToFail++ {
		if passed, err := runTestOnce(test, mallocNumToFail); err != errMoreMallocs {
			if err != nil {
				err = fmt.Errorf("at malloc %d: %s", mallocNumToFail, err)
			}
			return passed, err
		}
	}
}

func fileExists(filename string) bool {
	_, err := os.Stat(filename)
	return err == nil
}

// setWorkingDirectory walks up directories as needed until the current working
// directory is the top of a BoringSSL checkout.
func setWorkingDirectory() {
	for i := 0; i < 64; i++ {
		if fileExists("BUILDING.md") {
			return
		}
		os.Chdir("..")
	}

	panic("Couldn't find BUILDING.md in a parent directory!")
}

func worker(tests <-chan test, results chan<- result, done *sync.WaitGroup) {
	defer done.Done()
	for test := range tests {
		passed, err := runTest(test)
		results <- result{test, passed, err}
	}
}

func (t test) shortName() string {
	return strings.Join(t.Cmd, " ") + t.shardMsg() + t.cpuMsg() + t.envMsg()
}

func SpaceIf(returnSpace bool) string {
	if !returnSpace {
		return ""
	}
	return " "
}

func (t test) longName() string {
	return strings.Join(t.Env, " ") + SpaceIf(len(t.Env) != 0) + strings.Join(t.Cmd, " ") + t.shardMsg() + t.cpuMsg()
}

func (t test) shardMsg() string {
	if t.numShards == 0 {
		return ""
	}

	return fmt.Sprintf(" [shard %d/%d]", t.shard+1, t.numShards)
}

func (t test) cpuMsg() string {
	if len(t.cpu) == 0 {
		return ""
	}

	return fmt.Sprintf(" (for CPU %q)", t.cpu)
}

func (t test) envMsg() string {
	if len(t.Env) == 0 {
		return ""
	}

	return " (custom environment)"
}

func (t test) getGTestShards() ([]test, error) {
	if *numWorkers == 1 || !t.Shard {
		return []test{t}, nil
	}

	shards := make([]test, *numWorkers)
	for i := range shards {
		shards[i] = t
		shards[i].shard = i
		shards[i].numShards = *numWorkers
	}

	return shards, nil
}

func main() {
	flag.Parse()
	setWorkingDirectory()

	testCases, err := testconfig.ParseTestConfig("util/all_tests.json")
	if err != nil {
		fmt.Printf("Failed to parse input: %s\n", err)
		os.Exit(1)
	}

	var wg sync.WaitGroup
	tests := make(chan test, *numWorkers)
	results := make(chan result, *numWorkers)

	for i := 0; i < *numWorkers; i++ {
		wg.Add(1)
		go worker(tests, results, &wg)
	}

	go func() {
		for _, baseTest := range testCases {
			test := test{Test: baseTest}

			if !targetArchMatchesRuntime(test.TargetArch) {
				continue
			}

			if *useValgrind {
				if test.SkipValgrind {
					continue
				}
			}

			if !(*sslTests) {
				if strings.Contains(fmt.Sprint(test.Cmd), "ssl/") {
					continue
				}
			}

			if *useSDE {
				if test.SkipSDE {
					continue
				}
				// SDE generates plenty of tasks and gets slower
				// with additional sharding.
				for _, cpu := range sdeCPUs {
					testForCPU := test
					testForCPU.cpu = cpu
					tests <- testForCPU
				}
			} else {
				shards, err := test.getGTestShards()
				if err != nil {
					fmt.Printf("Error listing tests: %s\n", err)
					os.Exit(1)
				}
				for _, shard := range shards {
					tests <- shard
				}
			}
		}
		close(tests)

		wg.Wait()
		close(results)
	}()

	testOutput := testresult.NewResults()
	var failed, skipped []test
	for testResult := range results {
		test := testResult.Test
		args := test.Cmd

		if testResult.Error == errTestSkipped {
			fmt.Printf("%s\n", test.longName())
			fmt.Printf("%s was skipped\n", args[0])
			skipped = append(skipped, test)
			testOutput.AddSkip(test.longName())
		} else if testResult.Error == errTestHanging {
			if !testResult.Passed {
				fmt.Printf("%s\n", test.longName())
				fmt.Printf("%s did not finish. Try increasing timeout.\n", args[0])
				failed = append(failed, test)
				testOutput.AddResult(test.longName(), "FAIL")
			} else {
				fmt.Printf("%s\n", test.shortName())
				fmt.Printf("%s was left hanging, but actually passed\n", args[0])
				testOutput.AddResult(test.longName(), "PASS")
			}
		} else if testResult.Error != nil {
			fmt.Printf("%s\n", test.longName())
			fmt.Printf("%s failed to complete: %s\n", args[0], testResult.Error)
			failed = append(failed, test)
			testOutput.AddResult(test.longName(), "CRASH")
		} else if !testResult.Passed {
			fmt.Printf("%s\n", test.longName())
			fmt.Printf("%s failed to print PASS on the last line.\n", args[0])
			failed = append(failed, test)
			testOutput.AddResult(test.longName(), "FAIL")
		} else {
			fmt.Printf("%s\n", test.shortName())
			testOutput.AddResult(test.longName(), "PASS")
		}
	}

	if *jsonOutput != "" {
		if err := testOutput.WriteToFile(*jsonOutput); err != nil {
			fmt.Fprintf(os.Stderr, "Error: %s\n", err)
		}
	}

	if len(skipped) > 0 {
		fmt.Printf("\n%d of %d tests were skipped:\n", len(skipped), len(testCases))
		for _, test := range skipped {
			fmt.Printf("\t%s\n", test.shortName())
		}
	}

	if len(failed) > 0 {
		fmt.Printf("\n%d of %d tests failed:\n", len(failed), len(testCases))
		for _, test := range failed {
			fmt.Printf("\t%s\n", test.shortName())
		}
		os.Exit(1)
	}

	fmt.Printf("All unit tests passed!\n")
}
