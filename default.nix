{ sources ? import ./nix/sources.nix
, pkgs ? import sources.nixpkgs {
    overlays = [ ];
    config = { };
  }
}:

with pkgs;
let
  locales = {
    LANG = "en_US.UTF-8";
    LC_ALL = "en_US.UTF-8";
    LOCALE_ARCHIVE = pkgs.lib.optionalString
      pkgs.stdenv.isLinux
      "${pkgs.glibcLocales}/lib/locale/locale-archive";
  };

  agdaStdlib = agdaPackages.standard-library.overrideAttrs (oldAttrs: {
    version = "2.2";
    src = fetchFromGitHub {
      repo = "agda-stdlib";
      owner = "agda";
      rev = "v2.2";
      hash = "sha256-/Fy5EOSbVNXt6Jq0yKSnlNPW4SYfn+eCTAYFnMZrbR0=";
    };
  });

  agdaStdlibClasses = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-classes";
    version = "2.2.+";
    src = fetchFromGitHub {
      repo = "agda-stdlib-classes";
      owner = "agda";
      rev = "aa62ce6348d39c554ef89487079871d5590e155e";
      sha256 = "sha256-I/g0BOdeAHVEtsfmPBICySOd6Jz5ymGUSE/G66EfHK8=";
    };
    meta = { };
    libraryFile = "agda-stdlib-classes.agda-lib";
    everythingFile = "standard-library-classes.agda";
    buildInputs = [ agdaStdlib ];
  };

  agdaStdlibMeta = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-meta";
    version = "2.2.+";
    src = fetchFromGitHub {
      repo = "agda-stdlib-meta";
      owner = "agda";
      rev = "5ff853375180ef69f243ce72f2d3f6294bdb6aff";
      sha256 = "sha256-CNKEnDUToKEv+6Gaa8p5igLNpQDuasQ01JJLOXcU1bA=";
    };
    meta = { };
    libraryFile = "agda-stdlib-meta.agda-lib";
    everythingFile = "standard-library-meta.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  agdaSets = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-sets";
    version = "";
    src = fetchFromGitHub {
      repo = "agda-sets";
      owner = "input-output-hk";
      rev = "f517d0d0c1ff1fd6dbac8b34309dea0e1aea6fc6";
      sha256 = "sha256-OsdDNNJp9NWDgDM0pDOGv98Z+vAS1U8mORWF7/B1D7k=";
    };
    meta = { };
    libraryFile = "abstract-set-theory.agda-lib";
    everythingFile = "src/abstract-set-theory.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta ];
  };

  agdaIOGPrelude = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-prelude";
    version = "2.0";
    src = pkgs.fetchFromGitHub {
      repo = "iog-agda-prelude";
      owner = "input-output-hk";
      rev = "main";
      sha256 = "sha256-PvfxcoK5MweXfdtbfDUTY23xsaAG093MbeX9fRac4sQ=";
    };
    meta = { };
    libraryFile = "iog-prelude.agda-lib";
    everythingFile = "src/Everything.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  deps = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta agdaSets agdaIOGPrelude ];

  fs = pkgs.lib.fileset;
  addToAgdaSrc = other: fs.toSource {
    root = ./.;
    fileset = fs.unions ([ ./src ./praos-spec.agda-lib ] ++ other);
  };

in rec
{
  agdaWithDeps = agda.withPackages { pkgs = deps; };
}
