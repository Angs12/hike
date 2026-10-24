{
  description = "Hike: lift x86-64 ELF binaries to LLVM IR with the BAP fork";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    # The BAP fork owns its own build.  Follow this flake's nixpkgs so
    # BAP and Hike share one OCaml/LLVM instance.
    bap = {
      url = "github:Angs12/bap";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, bap }:
    let
      systems = [ "x86_64-linux" ];
      forAllSystems = f:
        nixpkgs.lib.genAttrs systems
          (system: f nixpkgs.legacyPackages.${system} system);
    in
    {
      packages = forAllSystems (pkgs: system:
        let
          ocamlPackages = pkgs.ocaml-ng.ocamlPackages_5_3;
          llvmPackages = pkgs.llvmPackages_19;

          # Nixpkgs' OCaml LLVM bindings track the default LLVM (21);
          # derive them from LLVM 19 instead.  They must link the shared
          # libLLVM so BAP's LLVM plugin and Hike share one cl registry.
          ocamlLlvm = (ocamlPackages.llvm.override {
            libllvm = llvmPackages.libllvm;
          }).overrideAttrs (old: {
            cmakeFlags =
              builtins.filter (f: f != "-DBUILD_SHARED_LIBS=YES")
                (old.cmakeFlags or [ ])
              ++ [ "-DLLVM_LINK_LLVM_DYLIB=ON" ];
            # Native-only stubs produce no stublibs directory.
            postInstall = ''
              mkdir -p $OCAMLFIND_DESTDIR/
              mv $out/ocaml $OCAMLFIND_DESTDIR/llvm
              mv $OCAMLFIND_DESTDIR/llvm/META{.llvm,}
              if [ -d $OCAMLFIND_DESTDIR/llvm/stublibs ]; then
                mv $OCAMLFIND_DESTDIR/llvm/stublibs $OCAMLFIND_DESTDIR/stublibs
              fi
            '';
          });

          bapPkg = bap.packages.${system}.bap;

          hikePkg = pkgs.callPackage ./nix/hike.nix {
            inherit ocamlPackages llvmPackages ocamlLlvm;
            bap = bapPkg;
            src = ./.;
          };

          corpusPkg = pkgs.callPackage ./nix/corpus.nix {
            src = ./.;
          };
        in
        {
          bap = bapPkg;
          hike = hikePkg;
          corpus = corpusPkg;
          # The gate scripts pin opt-19/llc-19; expose the matching tools.
          llvm19 = pkgs.llvmPackages_19.llvm;
          default = hikePkg;
        });

      checks = forAllSystems (pkgs: system: {
        unit = self.packages.${system}.hike.unit;
      });

      apps = forAllSystems (pkgs: system:
        {
          hike = {
            type = "app";
            program = "${self.packages.${system}.hike}/bin/hike";
            meta.description = "Lift an x86-64 ELF binary to LLVM IR";
          };
        });
    };
}
