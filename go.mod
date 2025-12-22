module boringssl.googlesource.com/boringssl

// When this changes update /cmake/go.cmake minimum_go_version and /BUILDING.md
go 1.17

require golang.org/x/crypto v0.17.0

require github.com/ethereum/go-ethereum v1.13.15

require (
	golang.org/x/sys v0.16.0 // indirect
	golang.org/x/term v0.15.0 // indirect
)
