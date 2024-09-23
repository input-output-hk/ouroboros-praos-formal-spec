{ repoRoot, inputs, pkgs, system, lib, ... }:

let
  cabalProject = pkgs.haskell-nix.cabalProject ({ pkgs, config, ... }: {
    src = ../.;
    shell.withHoogle = false;
    inputMap = {
      "https://input-output-hk.github.io/cardano-haskell-packages" =
        inputs.iogx.inputs.CHaP;
    };
    name = "praos-formal-spec";
    compiler-nix-name = lib.mkDefault "ghc96";
    flake.variants.profiled.modules = [{
      enableProfiling = true;
      enableLibraryProfiling = true;
    }];
  });

  project = lib.iogx.mkHaskellProject {
    inherit cabalProject;
    readTheDocs.enable = false;
    shellArgs = repoRoot.nix.shell;
  };

in project
