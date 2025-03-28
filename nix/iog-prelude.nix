{ repoRoot, pkgs, ... }:

repoRoot.nix.agda-packages.mkDerivation rec {
  pname = "iog-prelude";
  version = "2.0";
  src = pkgs.fetchFromGitHub {
    repo = "iog-agda-prelude";
    owner = "input-output-hk";
    rev = "35138185fee10c7bc604a13e63eafaa2e40ce7df";
    sha256 = "sha256-PvfxcoK5MweXfdtbfDUTY23xsaAG093MbeX9fRac4sQ=";
  };
  meta = { };
  libraryFile = "iog-prelude.agda-lib";
  everythingFile = "src/Everything.agda";
  buildInputs = [ repoRoot.nix.agda-stdlib repoRoot.nix.agda-stdlib-classes ];
}
