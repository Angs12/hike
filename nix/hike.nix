{ lib
, stdenv
, ocamlPackages
, dune_3
, makeWrapper
, llvmPackages
, ocamlLlvm
, z3
, gmp
, zlib
, libffi
, openssl
, ncurses
, readline
, libxml2
, sqlite
, curl
, pcre
, pcre2
, zstd
, bap
, src
}:

let
  llvm = llvmPackages.llvm;
  ocaml = ocamlPackages.ocaml;

  # Hike links the LLVM 19 OCaml bindings; BAP supplies the rest of the
  # OCaml graph (including the fork-only libraries).
  runtimeOcamlLibs = bap.ocamlDeps ++ [
    ocamlPackages.core
    ocamlLlvm
    ocamlPackages.seq
  ];

  siteLib = "lib/ocaml/${ocaml.version}/site-lib";
  # The loader resolves each plugin's findlib [requires] at runtime, so
  # the wrapper needs the OCaml packages' propagated closure, not just
  # the direct inputs.
  ocamlClosure = lib.closePropagation runtimeOcamlLibs;
  ocamlPath = "${lib.makeSearchPath siteLib ocamlClosure}:${ocaml}/lib/ocaml";
  stublibs = "${lib.makeSearchPath "${siteLib}/stublibs" ocamlClosure}:${ocaml}/lib/ocaml/stublibs";

  runtimeLibs = [
    bap
    ocamlPackages.ocaml
    llvm.lib
    z3
    gmp
    zlib
    libffi
    openssl
    ncurses
    readline
    libxml2
    sqlite
    curl
    pcre
    pcre2
    zstd
  ];
  libPath = lib.makeLibraryPath runtimeLibs;

  # Alcotest/fmt default to cmdliner 2.x; BAP links cmdliner 1.x, so the
  # test suite needs both rebuilt against the same interface.
  unitAlcotest =
    let
      cmdliner1 = ocamlPackages.cmdliner_1;
      fmt1 = ocamlPackages.fmt.override { cmdliner = cmdliner1; };
    in
    ocamlPackages.alcotest.override {
      cmdliner = cmdliner1;
      fmt = fmt1;
    };

  # The unit suite needs the same runtime graph as the CLI, plus alcotest.
  unit = stdenv.mkDerivation {
    pname = "hike-unit";
    version = "0.1.0";

    inherit src;

    nativeBuildInputs = [
      ocamlPackages.ocaml
      ocamlPackages.findlib
      dune_3
      ocamlPackages.ppx_jane
      ocamlPackages.cppo
      llvm
    ];

    buildInputs = [ bap ] ++ bap.ocamlDeps ++ [
      ocamlPackages.core
      # Alcotest defaults to cmdliner 2.x, but BAP links cmdliner 1.x.
      unitAlcotest
      ocamlLlvm
      llvm.lib
      llvm.dev
    ];

    dontDetectOcamlConflicts = true;

    postPatch = ''
      patchShebangs src/cppo_preprocess.sh
    '';

    preBuild = ''
      # Prepend BAP's findlib root; keep the path the Nix hook built
      # from the test's own inputs (alcotest included).
      export OCAMLPATH="${bap}/lib''${OCAMLPATH:+:$OCAMLPATH}"
      export BAP_PLUGIN_PATH="${bap}/lib/bap-common/plugins"
      export CAML_LD_LIBRARY_PATH="${bap}/lib/stublibs''${CAML_LD_LIBRARY_PATH:+:$CAML_LD_LIBRARY_PATH}"
      export LD_LIBRARY_PATH="${libPath}''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

      # BAP's cache plugin needs a writable home in the sandbox.
      export HOME="$TMPDIR/hike-home"
      export XDG_CACHE_HOME="$HOME/.cache"
      export XDG_STATE_HOME="$HOME/.local/state"
      export XDG_DATA_HOME="$HOME/.local/share"
      mkdir -p "$XDG_CACHE_HOME" "$XDG_STATE_HOME" "$XDG_DATA_HOME"
    '';

    buildPhase = ''
      runHook preBuild
      dune runtest test/unit --profile release --display short
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      mkdir -p "$out"
      touch "$out/unit-tests-passed"
      runHook postInstall
    '';
  };
in
stdenv.mkDerivation {
  pname = "hike";
  version = "0.1.0";

  inherit src;
  passthru = { inherit unit; };

  nativeBuildInputs = [
    ocamlPackages.ocaml
    ocamlPackages.findlib
    dune_3
    ocamlPackages.ppx_jane
    ocamlPackages.cppo
    makeWrapper
  ];

  buildInputs = [ bap ] ++ bap.ocamlDeps ++ [
    ocamlPackages.core
    ocamlPackages.bin_prot
    ocamlPackages.zarith
    ocamlPackages.sexplib
    ocamlPackages.ppx_sexp_conv
    ocamlPackages.ppx_compare
    ocamlLlvm
    llvm.lib
    llvm.dev
  ];

  dontDetectOcamlConflicts = true;

  # Dune executes this helper directly; give it a store-shell shebang.
  postPatch = ''
    patchShebangs src/cppo_preprocess.sh
  '';

  # BAP installs with dune's ordinary lib layout, so its package root is
  # the findlib path (Nix's hook only adds lib/ocaml/*/site-lib).
  preBuild = ''
    export OCAMLPATH="${bap}/lib''${OCAMLPATH:+:$OCAMLPATH}"
  '';

  buildPhase = ''
    runHook preBuild
    dune build src/drive/main.exe --profile release --display short
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    install -Dm755 _build/default/src/drive/main.exe "$out/bin/hike"
    install -Dm644 data/glibc.sexp "$out/share/hike/glibc.sexp"

    wrapProgram "$out/bin/hike" \
      --prefix BAP_PLUGIN_PATH : "${bap}/lib/bap-common/plugins" \
      --prefix OCAMLPATH : "${bap}/lib:${ocamlPath}" \
      --set DUNE_OCAML_HARDCODED "${bap}/lib:${ocamlPath}" \
      --set DUNE_OCAML_STDLIB "${ocaml}/lib/ocaml" \
      --prefix CAML_LD_LIBRARY_PATH : "${bap}/lib/stublibs:${stublibs}" \
      --prefix LD_LIBRARY_PATH : "${libPath}"
    runHook postInstall
  '';

  meta = with lib; {
    description = "Lifts x86-64 ELF binaries to LLVM IR through a value-set analysis";
    homepage = "https://github.com/Angs12/hike";
    license = licenses.mit;
    platforms = platforms.linux;
  };
}
