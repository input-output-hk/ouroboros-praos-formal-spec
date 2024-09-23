{ repoRoot, pkgs, ... }:

repoRoot.nix.agda-packages.mkDerivation rec {
  pname = "iog-prelude";
  version = "0.1.0.0";
  meta = { };
  src = pkgs.fetchFromGitHub {
    repo = "iog-agda-prelude";
    owner = "input-output-hk";
    rev = "v${version}";
    sha256 = "sha256-OV2WvQkjyGcfsgj81tkk/tIWHBUKsPia1d2Lh3F8qf4=";
  };
  preConfigure = ''
    mv src/Everything.agda Everything.agda
  '';
  buildInputs = [ repoRoot.nix.agda-stdlib ];
}
