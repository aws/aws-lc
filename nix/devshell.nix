{ pkgs, aws-lc }:
pkgs.mkShell rec {
  buildInputs =
    [ pkgs.cmake pkgs.nixfmt-classic pkgs.ninja pkgs.perl pkgs.go aws-lc ];

  shellHook = ''
    # Set custom prompt with ANSI color
    export PS1="\[\033[1;32m\][aws-lc]\[\033[0m\] $PS1"
    echo -e "\033[1;32mEntering AWS-LC development shell...\033[0m"
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
