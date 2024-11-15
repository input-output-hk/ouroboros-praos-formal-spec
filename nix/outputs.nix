{ repoRoot, inputs, pkgs, lib, system }:

let
  project = repoRoot.nix.project;
  ouroboros-praos-formal-spec = repoRoot.nix.ouroboros-praos-formal-spec;
in
[
  (project.flake)
  {
    inherit repoRoot;
    packages.ouroboros-praos-formal-spec = ouroboros-praos-formal-spec;
    devShells.profiled = project.variants.profiled.devShell;
  }
]
