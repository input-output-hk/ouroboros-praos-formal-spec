{ sources ? import ./nix/sources.nix
, pkgs ? import sources.nixpkgs {
    overlays = [ ];
    config = { };
  }
}:

with pkgs;

let
  specs = callPackage ./default.nix {};
  LOCALE_ARCHIVE = pkgs.lib.optionalString
    pkgs.stdenv.isLinux
    "${pkgs.glibcLocales}/lib/locale/locale-archive";
in {
  shell = mkShell {
    nativeBuildInputs = [
      specs.agdaWithDeps
      python310
      pkgs.glibcLocales
    ];

    shellHook = ''
      export LANG=en_US.UTF-8
      export LOCALE_ARCHIVE=${LOCALE_ARCHIVE}
    '';

  };

  run = {
    shell = mkShell {
      nativeBuildInputs = [
        specs.agdaWithDeps
        cabal-install
        pkgs.glibcLocales
      ];
      shellHook = ''
        export LANG=en_US.UTF-8
        export LOCALE_ARCHIVE=${LOCALE_ARCHIVE}
      '';
    };
  };
}
