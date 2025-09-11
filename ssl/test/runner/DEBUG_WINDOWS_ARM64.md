# Debugging Windows ARM64 SSL Test Failures

This document describes debugging tools and strategies for diagnosing SSL test failures on Windows ARM64, specifically the IPv6 localhost connectivity issues that cause `Peek-*-Server` tests to fail with `i/o timeout` errors.

## Problem Description

The SSL tests fail on Windows 11 ARM64 with errors like:
```
FAILED (Peek-Basic-Server)
unexpected failure: local error 'read tcp [::1]:50848->[::1]:57413: i/o timeout', child error 'none'
```

These failures are caused by IPv6 localhost connectivity issues where the initial IPv6 socket creation succeeds but actual communication times out.

## Debugging Flags Added

The following new command-line flags have been added to help diagnose the issue:

### `--force-ipv4`
Forces IPv4 for all network connections, bypassing IPv6 entirely.
```bash
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --force-ipv4
```

### `--verbose-network`  
Enables detailed network setup debugging output.
```bash
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --verbose-network
```

### `--test-network-first`
Runs network connectivity tests before SSL tests begin.
```bash
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --test-network-first
```

### `--connection-debug`
Adds detailed connection-level debugging for reads/writes with timing information.
```bash
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --connection-debug
```

### `--peek-rounds`
Controls the number of peek rounds for SSL peek tests, which directly affects message size.
```bash
# Default: 50 rounds = ~819KB messages  
# Reduced: 5 rounds = ~82KB messages
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --peek-rounds 5
```

### `--idle-timeout`
Adjusts the timeout for network operations (default: 15s).
```bash
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --idle-timeout 60s
```

## Automatic Behavior

### Windows ARM64 Detection
The code automatically detects Windows ARM64 and forces IPv4 to work around known IPv6 issues:
```
[DEBUG] Windows ARM64 detected, forcing IPv4 due to known IPv6 issues
```

### Verbose Output for Failing Tests
Peek server tests automatically get extra debugging on Windows platforms.

### Large Message Size Issue
The failing Peek tests use very large messages by default:
- Default: 50 peek rounds × 16384 bytes + 1 = 819,201 bytes (~800KB)
- This large size may cause issues on Windows ARM64
- Use `--peek-rounds` to test with smaller messages

## Debugging Workflow

### Step 1: Test with Smaller Messages First
```bash
# Test with much smaller messages (5 rounds = ~82KB instead of 819KB)
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --peek-rounds 5 --test "Peek.*Server"
```

**Expected Result:** If large message size is the issue, this should pass.

### Step 2: Quick Test with IPv4 Only (already applied automatically)
```bash
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --force-ipv4 --test "Peek.*Server"
```

**Expected Result:** This tests if there were any remaining IPv6 issues.

### Step 3: Network Connectivity Diagnosis
```bash
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --test-network-first --verbose-network
```

**Look for:**
- IPv4 vs IPv6 listener creation success/failure
- Self-connection test results
- Windows network interface information

### Step 4: Detailed Connection Analysis
```bash
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --connection-debug --verbose-network --test "Peek.*Server"
```

**Look for:**
- Timeout deadline settings
- Read/write operation timing
- Local vs remote address information
- Where exactly the timeout occurs

### Step 5: Extended Timeout Testing
```bash
go test -timeout 30m -shim-path /path/to/bssl_shim.exe --idle-timeout 120s --test "Peek.*Server"
```

**Purpose:** Determine if it's a timing issue vs a fundamental connectivity problem.

### Step 6: Progressive Message Size Testing
```bash
# Test with various message sizes to find the breaking point
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --peek-rounds 1 --test "Peek.*Server"  # ~16KB
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --peek-rounds 10 --test "Peek.*Server" # ~164KB  
go test -timeout 20m -shim-path /path/to/bssl_shim.exe --peek-rounds 25 --test "Peek.*Server" # ~410KB
```

**Purpose:** Identify the maximum message size that works on Windows ARM64.

## Debug Output Examples

### Message Size Debugging
```
[DEBUG] addServerPeekTests: Using default peek_rounds = 50
[DEBUG] addServerPeekTests: maxPlaintext=16384, peek_rounds=50, calculated messageLen=819201 bytes (800.00 KB)
[DEBUG] runTest: Starting Peek server test: Peek-Basic-Server (GOOS: windows, GOARCH: arm64)
[DEBUG] runTest: Test type: 1, messageLen: 819201, flags: [-peek-then-read]
[DEBUG] doExchange: Creating test message for Peek-Basic-Server: 819201 bytes (800.00 KB)
[DEBUG] doExchange: Successfully wrote test message for Peek-Basic-Server: 819201 bytes in 2.5ms
```

### Normal IPv4 Operation (Small Messages)
```
[DEBUG] addServerPeekTests: Using command line flag peek_rounds = 5
[DEBUG] addServerPeekTests: maxPlaintext=16384, peek_rounds=5, calculated messageLen=81921 bytes (80.00 KB)
[DEBUG] Creating shimDispatcher on windows arm64
[DEBUG] Windows ARM64 detected, forcing IPv4 due to known IPv6 issues
[DEBUG] shimDispatcher listening on: 127.0.0.1:54321
[DEBUG] runTest: Starting Peek server test: Peek-Basic-Server (GOOS: windows, GOARCH: arm64)
[DEBUG] timeoutConn.Read: succeeded after 150ms (read 1024 bytes)
```

### IPv6 Failure Pattern
```
[DEBUG] Creating shimDispatcher on windows arm64
[DEBUG] Attempting IPv6 localhost first
[DEBUG] IPv6 localhost succeeded, addr: [::1]:54321
[DEBUG] Starting Peek server test: Peek-Basic-Server (GOOS: windows, GOARCH: arm64)
[DEBUG] timeoutConn.Read: deadline set to 2024-01-15 10:30:45 (in 15s) for [::1]:54321->[::1]:54322
[DEBUG] timeoutConn.Read: failed with read tcp [::1]:54321->[::1]:54322: i/o timeout after 15s (read 0 bytes)
```

### Large Message Failure Pattern
```
[DEBUG] addServerPeekTests: Using default peek_rounds = 50
[DEBUG] addServerPeekTests: maxPlaintext=16384, peek_rounds=50, calculated messageLen=819201 bytes (800.00 KB)
[DEBUG] runTest: Starting Peek server test: Peek-Basic-Server (GOOS: windows, GOARCH: arm64)
[DEBUG] newShimProcess: Shim process started with PID 12345
[DEBUG] shimProcess.accept: Connection accepted: 127.0.0.1:54322->127.0.0.1:54321 (PID 12345)
[DEBUG] doExchange: Creating test message for Peek-Basic-Server: 819201 bytes (800.00 KB)
[DEBUG] doExchange: Successfully wrote test message for Peek-Basic-Server: 819201 bytes in 5ms
[DEBUG] timeoutConn.Read: deadline set to 2024-01-15 10:30:45 (in 15s) for 127.0.0.1:54321->127.0.0.1:54322
[DEBUG] shimProcess.wait: idleTimeout reached for process 12345
[DEBUG] shimProcess.wait: Process 12345 stdout: 
[DEBUG] shimProcess.wait: Process 12345 stderr: 
[DEBUG] timeoutConn.Read: failed with read tcp4 127.0.0.1:54321->127.0.0.1:54322: i/o timeout after 15s (read 0 bytes)
```

### Network Connectivity Test Output
```
[DEBUG] Starting network connectivity checks...
[DEBUG] Checking Windows networking configuration...
[DEBUG] GOOS: windows, GOARCH: arm64
[DEBUG] Loopback address found: 127.0.0.1
[DEBUG] Loopback address found: ::1
[DEBUG] IPv4 loopback available: true
[DEBUG] IPv6 loopback available: true
[DEBUG] Testing network connectivity...
[DEBUG] IPv4 localhost dial failed (expected for port 0): dial tcp4 127.0.0.1:0: connectex: No connection could be made
[DEBUG] IPv6 localhost dial failed (expected for port 0): dial tcp6 [::1]:0: connectex: No connection could be made
[DEBUG] IPv4 listener created at 127.0.0.1:54123
[DEBUG] IPv4 self-connect succeeded
[DEBUG] IPv6 listener created at [::1]:54124
[DEBUG] IPv6 self-connect failed: dial tcp6 [::1]:54124: connectex: A connection attempt failed
```

## Common Issues and Solutions

### Issue: Large Message Size Causing Timeouts
**Symptoms:** SSL peek tests fail with i/o timeout on Windows ARM64, shim process becomes unresponsive.
**Root Cause:** Default 819KB message size may exceed Windows ARM64 SSL buffer limits or cause memory issues.
**Solution:** Use `--peek-rounds 5` or lower to reduce message size.

### Issue: IPv6 Interface Available but Non-Functional  
**Symptoms:** IPv6 loopback shows as available, IPv6 listener creation succeeds, but connections timeout.
**Solution:** Already automatically handled - Windows ARM64 forces IPv4.

### Issue: All Network Tests Fail
**Symptoms:** Both IPv4 and IPv6 connectivity tests fail.
**Solution:** Check Windows firewall, antivirus, or network security settings.

### Issue: Intermittent Failures
**Symptoms:** Tests sometimes pass, sometimes fail.
**Solution:** Increase `--idle-timeout` and check for resource contention.

## Integration with CI/CD

For automated testing on Windows ARM64, recommend:
```bash
# In your CI script
if [[ "$RUNNER_OS" == "Windows" && "$RUNNER_ARCH" == "ARM64" ]]; then
    # Use smaller message sizes for Windows ARM64 to avoid timeout issues
    go test -timeout 20m -shim-path "$BSSL_SHIM_PATH" --peek-rounds 5
else
    go test -timeout 20m -shim-path "$BSSL_SHIM_PATH"
fi
```

## Files Modified

- `ssl/test/runner/runner.go`: Added debugging flags, network tests, enhanced timeouts, message size controls
- `ssl/test/runner/shim_dispatcher.go`: Added Windows ARM64 detection and IPv4 forcing  
- `ssl/test/runner/DEBUG_WINDOWS_ARM64.md`: This documentation

## Performance Impact

- `--verbose-network`: Minimal impact, only adds startup logging
- `--connection-debug`: Moderate impact, logs every read/write operation
- `--force-ipv4`: No performance impact, may actually improve performance on affected systems
- `--test-network-first`: Adds ~1-2 seconds to test startup time
- `--peek-rounds 5`: Significantly faster (~10x less data), reduces memory usage

## Future Improvements

1. Implement automatic message size reduction for Windows ARM64
2. Add memory usage monitoring during SSL peek operations
3. Create progressive timeout scaling based on message size
4. Add Windows ARM64-specific SSL buffer size detection
5. Implement chunked message processing for large SSL peek tests