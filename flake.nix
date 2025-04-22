{
  description = "AWS-LC is a general-purpose cryptographic library";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";

  outputs = { self, nix, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        shells = import ./nix/devshell.nix { pkgs = pkgs; };

      in rec {
        packages.aws-lc = pkgs.stdenv.mkDerivation {
          src = self;
          name = "aws-lc";
          inherit system;
          nativeBuildInputs = [ pkgs.ninja pkgs.cmake pkgs.perl pkgs.go ];
          cmakeFlags = [
            "-GNinja"
            "-DBUILD_SHARED_LIBS=ON"
            "-DCMAKE_BUILD_TYPE=RelWithDebInfo"
          ];
          checkPhase = ''
            ninja run_minimal_tests
          '';
        };
        formatter = pkgs.nixfmt;
        packages.default = packages.aws-lc;
        devShells.default = shells;
      });
}

