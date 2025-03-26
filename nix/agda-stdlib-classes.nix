{ repoRoot, pkgs, ... }:

repoRoot.nix.agda-packages.mkDerivation rec {
  pname = "agda-stdlib-classes";
  version = "2.0";

  src = pkgs.fetchFromGitHub {
    repo = "agda-stdlib-classes";
    owner = "omelkonian";
    rev = "2b42a6043296b4601134b8ab9371b37bda5d4424";
    sha256 = "sha256-kTqS9p+jjv34d4JIWV9eWAI8cw9frX/K9DHuwv56AHo=";
  };
  meta = { };
  libraryFile = "agda-stdlib-classes.agda-lib";
  everythingFile = "standard-library-classes.agda";
  buildInputs = [ repoRoot.nix.agda-stdlib ];
}
