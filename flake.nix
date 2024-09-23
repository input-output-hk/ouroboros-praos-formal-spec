{
  description = "praos-formal-spec";

  inputs = {
    iogx = {
      url = "github:input-output-hk/iogx";
      inputs.hackage.follows = "hackage";
    };
    hackage = {
      url = "github:input-output-hk/hackage.nix";
      flake = false;
    };
    crane.url = "github:ipetkov/crane";
    crane.inputs.nixpkgs.follows = "nixpkgs";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = inputs:
    inputs.iogx.lib.mkFlake rec {
      inherit inputs;
      repoRoot = ./.;
      outputs = import ./nix/outputs.nix;
      systems = [ "x86_64-linux" "x86_64-darwin" "aarch64-darwin" ];
      # debug = false;
    };
}
