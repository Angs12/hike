let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-23.05";
  pkgs = import nixpkgs {
    config = { };
    overlays = [ ];
  };

in pkgs.mkShell {
  packages = with pkgs; [
    gcc12
    gnumake
    clang_15
    ocaml
    ocamlPackages.bap
    ocamlPackages.z3
  ];
  shellHook = ''
    cd src;
    make sim
  '';
}
