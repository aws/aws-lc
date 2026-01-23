module github.com/aws/aws-lc

// When this changes update /cmake/go.cmake minimum_go_version and /BUILDING.md
go 1.17

// v0.14.0 was the last version that support 1.17
require golang.org/x/crypto v0.14.0

require (
	golang.org/x/sys v0.13.0 // indirect
	golang.org/x/term v0.13.0 // indirect
)
