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
    version = "2.3";
    src = fetchFromGitHub {
      repo = "agda-stdlib";
      owner = "agda";
      rev = "v2.3";
      sha256 = "17w5vfn5pb2cgfs22zph3jfqnki52ja8y4zwyqj24zwf9rxairr4";
      url = "https://github.com/agda/agda-stdlib/archive/v2.3.tar.gz";
    };
  });

  agdaStdlibClasses = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-classes";
    version = "2.3";
    src = fetchFromGitHub {
      repo = "agda-stdlib-classes";
      owner = "agda";
      rev = "v2.3";
      sha256 = "0bbgc3nf1b2v3wljrq7974z38apzzsdhfzc1fdmm4fsmnpglmb1m";
      url = "https://github.com/agda/agda-stdlib-classes/archive/v2.3.tar.gz";
    };
    meta = { };
    libraryFile = "agda-stdlib-classes.agda-lib";
    everythingFile = "standard-library-classes.agda";
    buildInputs = [ agdaStdlib ];
  };

  agdaStdlibMeta = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-stdlib-meta";
    version = "2.3";
    src = fetchFromGitHub {
      repo = "agda-stdlib-meta";
      owner = "agda";
      rev = "v2.3";
      sha256 = "1n41cfkahg2zzfm113dkqlh5m07rvm9jjh8ps50qi3cpkz203gla";
      url = "https://github.com/agda/agda-stdlib-meta/archive/v2.3.tar.gz";
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
      rev = "31512b000317a577230e9ba5081b693801104851";
      sha256 = "1yj8a8r17y1pld87329cjvmfnha7ih5zan3wccc3sq661apr17l8";
      url = "https://github.com/input-output-hk/agda-sets/archive/31512b000317a577230e9ba5081b693801104851.tar.gz";
    };
    meta = { };
    libraryFile = "abstract-set-theory.agda-lib";
    everythingFile = "src/abstract-set-theory.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta ];
  };

  agdaIOGPrelude = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-prelude";
    version = "";
    src = pkgs.fetchFromGitHub {
      repo = "iog-agda-prelude";
      owner = "input-output-hk";
      rev = "cb11de4ab47db30a2e235e0c69f5876efad230ad";
      sha256 = "sha256-fRFbYtjxe2FhONAegSm+GBhbIBICRXfKotBIOTWOx/o=";
      url = "https://github.com/input-output-hk/iog-agda-prelude/archive/cb11de4ab47db30a2e235e0c69f5876efad230ad.tar.gz";
    };
    meta = { };
    libraryFile = "iog-prelude.agda-lib";
    everythingFile = "src/Everything.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta ];
  };

  agdaIrrelevance = agdaPackages.mkDerivation {
    inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
    pname = "agda-irrelevance";
    version = "2.3";
    src = pkgs.fetchFromGitHub {
      repo = "agda-irrelevance";
      owner = "omelkonian";
      rev = "main";
      sha256 = "sha256-7AvwgVPdiNe3/cuXF2Pm2LvQv0G645Gq90H5dgYbn+I=";
    };
    meta = { };
    libraryFile = "agda-irrelevance.agda-lib";
    everythingFile = "Irrelevance.agda";
    buildInputs = [ agdaStdlib agdaStdlibClasses ];
  };

  deps = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta agdaSets agdaIOGPrelude agdaIrrelevance ];

  fs = pkgs.lib.fileset;
  addToAgdaSrc = other: fs.toSource {
    root = ./.;
    fileset = fs.unions ([ ./src ./praos-spec.agda-lib ] ++ other);
  };

in rec
{
  agdaWithDeps = agda.withPackages { pkgs = deps; };
}
