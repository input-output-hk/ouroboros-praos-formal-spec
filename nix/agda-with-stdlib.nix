{ repoRoot, ... }:

let
  stdlib = repoRoot.nix.agda-stdlib;
  iog-prelude = repoRoot.nix.iog-prelude;
in repoRoot.nix.agda-packages.agda.withPackages [ stdlib iog-prelude ]
