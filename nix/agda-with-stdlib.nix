{ repoRoot, ... }:

let
  stdlib = repoRoot.nix.agda-stdlib;
  iog-prelude = repoRoot.nix.iog-prelude;
  agda-stdlib-classes = repoRoot.nix.agda-stdlib-classes;
in
repoRoot.nix.agda-packages.agda.withPackages [ stdlib agda-stdlib-classes iog-prelude ]
