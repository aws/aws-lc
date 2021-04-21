### Convert delocate.peg to delocate.peg.go

```shell script
# Clone peg.
git clone https://github.com/pointlander/peg
cd peg

# Building.
go run build.go

# After build, 'peg' executable is available under current dir.
# Below command can tell the https://github.com/pointlander/peg#usage
./peg --help
```           
