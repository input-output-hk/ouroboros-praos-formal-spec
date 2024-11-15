{ repoRoot, ... }:

repoRoot.nix.agda-packages.mkDerivation {
  version = "1.0";
  pname = "ouroboros-praos-formal-spec";
  src = ./..;
  meta = { description = "Ouroboros Praos formal specification"; };
  buildInputs = [ repoRoot.nix.agda-stdlib repoRoot.nix.iog-prelude ];
  everythingFile = "./src/Everything.agda";
  preBuild = ''
    # Create the missing everything file.
    find src -type f -name '*.lagda.md' | sed -e 's@^src/@import @; s@\.lagda\.md$@@ ; s@/@.@g' > Everything.agda
    sed -i '1imodule Everything where' Everything.agda
    mv Everything.agda src/
  '';
}
