{ repoRoot, inputs, pkgs, lib, system }:

let
  project = repoRoot.nix.project;
  praos-agda = repoRoot.nix.praos-agda;
in
[
  (project.flake)
  {
    inherit repoRoot;
    packages.praos = praos-agda;
    devShells.profiled = project.variants.profiled.devShell;
  }
]
