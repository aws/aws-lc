{
  description = "AWS-LC is a general-purpose cryptographic library";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.11";

  outputs = { self, nix, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        dashells = import ./nix/devshell.nix { pkgs = pkgs; };
        writeScript = path:
          pkgs.writeScript (baseNameOf path) (builtins.readFile path);
      in rec {
        packages.aws-lc = pkgs.stdenv.mkDerivation {
          src = self;
          name = "aws-lc";
          inherit system;
          nativeBuildInputs = [ pkgs.ninja pkgs.cmake pkgs.perl pkgs.golang ];
          cmakeFlags = [ "-GNinja" ];
          checkPhase = ''
            ninja run_minimal_tests
          '';
        };
        formatter = pkgs.nixfmt;
        packages.default = packages.aws-lc;
        devShells.default = dashells;
      });
}

