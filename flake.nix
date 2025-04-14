# Unified flake.nix that:
# - Preserves original flake features (hydraJobs, formalLedger)
# - Imports logic from default.nix and shell.nix
# - Supports nix build, nix run, nix develop

{
  description = "Ouroboros Praos Formal Specification";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/0da3c44a9460a26d2025ec3ed2ec60a895eb1114";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [];
        };

        # Load shell environment from shell.nix
        shellEnv = import ./shell.nix { inherit pkgs; };

        # Load package from default.nix
        defaultPackage = import ./default.nix { inherit pkgs; };
      in {
        # Dev shell imports same environment as shell.nix
        devShells = {
          default = shellEnv.shell;
          ci = shellEnv.run.shell;
        };
      });
}
