{
  description = "AWS-LC is a general-purpose cryptographic library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        aws-lc = pkgs.stdenv.mkDerivation {
          src = self;
          name = "aws-lc";
          inherit system;
          nativeBuildInputs = [ pkgs.ninja pkgs.cmake pkgs.perl pkgs.go ];
          # Workaround builds trying to write to $HOME: https://github.com/NixOS/nix/issues/670
          preBuild = ''
            export HOME=$PWD
          '';
          cmakeFlags = [
            "-GNinja"
            "-DBUILD_SHARED_LIBS=ON"
            "-DCMAKE_BUILD_TYPE=RelWithDebInfo"
          ];
          checkPhase = ''
            ninja run_minimal_tests
          '';
        };
        shells = import ./nix/devshell.nix {
          inherit pkgs;
          inherit aws-lc;
        };

      in rec {
        packages.aws-lc = aws-lc;
        formatter = pkgs.nixfmt;
        packages.default = packages.aws-lc;
        devShells.default = shells;
      });
}
