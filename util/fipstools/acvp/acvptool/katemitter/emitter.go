// katemitter is a package which (with best effort) will attempt to emit test case data to a configured file
// for use by AWS-LC's file-based test framework. "Attempt" because it doesn't check for errors on the writer
// destination. But this is mostly a facility to aid in getting KATs for algorithms and re-using the inputs/outputs
// from the ACVP server after they have been validated as accurate.
package katemitter

import (
	"bytes"
	"encoding/hex"
	"fmt"
	"io"
	"os"
)

type stubEmitter struct{}

func (s *stubEmitter) Close() error {
	return nil
}

func (s *stubEmitter) Write(p []byte) (n int, err error) {
	return len(p), nil
}

var katDestination io.WriteCloser = &stubEmitter{}

func EmitToFile(path string) error {
	if err := Close(); err != nil {
		return err
	}

	f, err := os.Create(path)
	if err != nil {
		return err
	}

	katDestination = f

	return nil
}

func NewTestCase(comment string) {
	var buffer bytes.Buffer
	buffer.WriteRune('\n')
	buffer.WriteString("# Case: ")
	buffer.WriteString(comment)
	buffer.WriteRune('\n')
	_, _ = io.Copy(katDestination, &buffer)
}

func NewSection(title string) {
	var buffer bytes.Buffer
	buffer.WriteRune('\n')
	buffer.WriteString("# Section: ")
	buffer.WriteString(title)
	buffer.WriteByte('\n')
	_, _ = io.Copy(katDestination, &buffer)
}

func WriteComment(comment string) {
	_, _ = katDestination.Write([]byte("# " + comment + "\n"))
}

func WriteStringKvPair(key string, value string) {
	_, _ = katDestination.Write([]byte(fmt.Sprintf("%s = %s\n", key, value)))
}

func WriteBytesKvPair(key string, value []byte) {
	_, _ = katDestination.Write([]byte(fmt.Sprintf("%s = %s\n", key, hex.EncodeToString(value))))
}

func WriteIntKvPair(key string, value int) {
	_, _ = katDestination.Write([]byte(fmt.Sprintf("%s = %d\n", key, value)))
}

func WriteInt64KvPair(key string, value int64) {
	_, _ = katDestination.Write([]byte(fmt.Sprintf("%s = %d\n", key, value)))
}

func WriteUInt64KvPair(key string, value uint64) {
	_, _ = katDestination.Write([]byte(fmt.Sprintf("%s = %d\n", key, value)))
}

func Close() error {
	_, _ = katDestination.Write([]byte("\n"))
	return katDestination.Close()
}
