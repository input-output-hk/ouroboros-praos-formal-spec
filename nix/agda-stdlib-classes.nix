{ repoRoot, pkgs, ... }:

repoRoot.nix.agda-packages.mkDerivation rec {
  pname = "agda-stdlib-classes";
  version = "2.0";

  src = pkgs.fetchFromGitHub {
    repo = "agda-stdlib-classes";
    owner = "omelkonian";
    rev = "28df278381c94a25c54f6819524cd9f8cb99f092";
    sha256 = "sha256-TdPJ3K4jyAIQgX1sUrqd0QeA72n2mkBVzlg8WfrqWWY=";
  };
  meta = { };
  libraryFile = "agda-stdlib-classes.agda-lib";
  everythingFile = "standard-library-classes.agda";
  buildInputs = [ repoRoot.nix.agda-stdlib ];
}
