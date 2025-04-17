{ pkgs }:
pkgs.mkShell rec {
  buildInputs = [ pkgs.cmake ];
  packages = [ pkgs.nixfmt-classic pkgs.ninja pkgs.cmake pkgs.perl pkgs.go ];
  shellHook = ''
    echo "Entering a devShell..."
    export PS1="[awslc nix] $PS1"
    function clean {(set -e
      rm -rf ./build
    )}
    function configure {(set -e
      cmake -S . -B./build \
        -GNinja \
        -DBUILD_SHARED_LIBS=ON \
        -DCMAKE_BUILD_TYPE=RelWithDebInfo
    )}
    function build {
        cmake --build ./build -j $(nproc)
    }
    function unit {
        ninja -C build run_tests
    }
  '';
}
