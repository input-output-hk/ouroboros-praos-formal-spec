{ repoRoot, pkgs, lib, ... }:

cabalProject:

{
  name = "ouroboros-praos-formal-spec";

  packages = with pkgs; [

    # Agda packages.
    repoRoot.nix.agda-with-stdlib
    repoRoot.nix.agda-stdlib
    repoRoot.nix.agda-stdlib-classes
    repoRoot.nix.iog-prelude
    repoRoot.nix.emacs-with-packages

    # Additional Haskell tools.
    # haskellPackages.pointfree
    # haskellPackages.pointful

    # Additional tools
    gnumake # For make-based Agda builds.
    # graphviz # For plotting network topology and chain forking.
    # haskellPackages.threadscope # For visualizing profiles.
    # ghostscript_headless # For visualizing profiles.
    # plantuml # For UML diagrams.
    # pandoc # For generating PDF from markdown.
    # librsvg # SVG conversion in pandoc.
    mononoki # Font for Agda.
    julia-mono # Font for Agda.

  ];

  tools = {
    # haskellCompilerVersion = cabalProject.args.compiler-nix-name;
    # cabal-fmt = null;
    # cabal-install = null;
    # haskell-language-server = null;
    # haskell-language-server-wrapper = null;
    # fourmolu = null;
    # hlint = null;
    # stylish-haskell = null;
    # ghcid = null;
    # shellcheck = null;
    # prettier = null;
    # editorconfig-checker = null;
    # nixpkgs-fmt = null;
    # optipng = null;
    # purs-tidy = null;
  };

  preCommit = {
    # cabal-fmt.enable = false;
    # cabal-fmt.extraOptions = "";
    # fourmolu.enable = true;
    # fourmolu.extraOptions = "";
    # hlint.enable = false;
    # hlint.extraOptions = "";
    # shellcheck.enable = false;
    # shellcheck.extraOptions = "";
    # editorconfig-checker.enable = false;
    # editorconfig-checker.extraOptions = "";
    nixpkgs-fmt.enable = true;
    # nixpkgs-fmt.extraOptions = "";
    # optipng.enable = false;
    # optipng.extraOptions = "";
  };
}

