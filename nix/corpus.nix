{ lib
, stdenv
, gcc
, binutils
, python3
, src
}:

stdenv.mkDerivation {
  pname = "hike-corpus";
  version = "0.1.0";

  inherit src;

  nativeBuildInputs = [ gcc binutils python3 ];

  dontConfigure = true;
  dontBuild = true;

  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    bash test/gate/compile_corpus.sh "$out"
    runHook postInstall
  '';

  meta = with lib; {
    description = "The PIE-only x86-64 test corpus for Hike";
    platforms = platforms.linux;
  };
}
