module boringssl.googlesource.com/boringssl

// When this changes update /cmake/go.cmake minimum_go_version and /BUILDING.md
go 1.24.0

require golang.org/x/crypto v0.36.0

require github.com/ethereum/go-ethereum v1.16.8

require (
	golang.org/x/sys v0.36.0 // indirect
	golang.org/x/term v0.30.0 // indirect
)
