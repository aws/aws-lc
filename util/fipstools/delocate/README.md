### Convert delocate.peg to delocate.peg.go

Below shell script should be execute under the directory having `delocate.peg`.
```shell script
# Clone peg.
git clone https://github.com/pointlander/peg
cd peg

# Building.
go run build.go

# After build, 'peg' executable is available under current dir.
# Below command can tell the https://github.com/pointlander/peg#usage
./peg --help

# Generate delocate.peg.go by running below command.
cd ..
./peg/peg delocate.peg

# Clean up.
rm -rf peg
```           
