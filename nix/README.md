# BAP + Hike Nix packages

The build is split across two flakes:

- the **BAP fork** carries its own `flake.nix`, which builds the complete
  BAP (all plugins and semantics, no filtering) and owns its LLVM pin;
- **this repo** carries the Hike flake, which takes that BAP flake as an
  input, builds the standalone `hike` CLI and the corpus, and shares one
  nixpkgs/OCaml instance with BAP via `bap.inputs.nixpkgs.follows`.

The BAP input is `github:Angs12/bap`, so the Hike lock pins a real BAP
commit rather than a local checkout.

Nixpkgs is pinned to `nixos-unstable` and both flakes select
`llvmPackages_19`, so BAP and Hike use the project's LLVM 19 toolchain.
Hike's `dune-project` needs dune 3.23, which is why the whole build stays on
unstable rather than the 25.05 channel (LLVM 19 default, dune 3.18).  The
OCaml bindings are additionally linked against the shared `libLLVM`: BAP's
LLVM plugin loads that library too, and a static copy in the executable
would create a second LLVM command-line registry (`-x86-asm-syntax`
unknown).

There is no opam switch and no dev shell.  Nixpkgs supplies OCaml 5.3 and
the external OCaml graph; the BAP fork builds the libraries Nixpkgs does
not package (`bitvec`, `graphlib`, `monads`, `ogre`, `regular`,
`text-tags`, `ppx_bap`).

Flakes are not enabled by default in this shell:

```sh
export NIX_CONFIG='experimental-features = nix-command flakes'
```

## Packages

| Output | Contents |
|---|---|
| `.#bap` | The BAP fork, its plugins and semantics, and the fork-local OCaml libraries |
| `.#hike` | The standalone `hike` CLI (not the BAP plugin), wrapped with the BAP plugin and OCaml runtime paths |
| `.#corpus` | The PIE-only x86-64 test corpus, built with Nix GCC |
| `.#llvm19` | The LLVM 19 tools (`opt`, `llc`) the gates pin |

Build everything:

```sh
nix build .#bap .#hike .#corpus
```

`nix build` links the last build as `./result` and prints no path. Name the
link you want, or ask for the store path:

```sh
nix build --out-link result-hike .#hike
nix build --print-out-paths .#hike   # /nix/store/...-hike-0.1.0
```

## Run

`nix run` needs no path:

```sh
nix run .#hike -- binary \
  --signatures "$(nix build --print-out-paths .#hike)/share/hike/glibc.sexp" \
  -o binary.ll
```

Or use a named link:

```sh
nix build --out-link result-hike .#hike
result-hike/bin/hike binary \
  --signatures result-hike/share/hike/glibc.sexp \
  -o binary.ll
```

`hike` requires explicit signature files; the installed copy of
`data/glibc.sexp` is at `$out/share/hike/glibc.sexp`.

The BAP package installs the complete plugin set; nothing is pruned.  The
`hike` wrapper puts the propagated OCaml library closure on `OCAMLPATH`
and `CAML_LD_LIBRARY_PATH`, because BAP's plugin loader resolves each
plugin's findlib `requires` at startup.

## Gates

The `gate` app wires the installed executable, the BAP library root, the
corpus and the pinned LLVM 19 tools, so no environment variables are needed:

```sh
nix run .#gate -- lift
nix run .#gate -- allocas       # Python 3 is in the app
nix run .#gate -- semantics     # opt-19/llc-19 are in the app
nix run .#gate -- performance
```

`corpus`, `unit`, `referee`, `sysv` and `all` build or write into the
source tree, so run those from the checkout with `bash test/gate/gate.sh`
and the switch's `dune`.

Outside Nix the scripts find `hike` on `PATH` (a bare `HIKE_EXE` name is
resolved there too) and derive the BAP library root from `BAP_PLUGIN_PATH`
or `ocamlfind query bap`; `HIKE_EXE`, `HIKE_LIBDIR`, `HIKE_CORPUS`,
`HIKE_EMIT`, `HIKE_SEMOUT` and `HIKE_LLC` still override.  `make lift` and
`make semantics` pass the opam switch's paths for you.  The app pins this
flake's executable and BAP root; the corpus, emit directories and renderer
remain overridable.

## Checks

The unit suite is a Nix check, run against the same BAP/LLVM instance:

```sh
nix build .#checks.x86_64-linux.unit
```

It runs `dune runtest test/unit`, not the whole `@runtest` alias: the CLP
allocation tripwire is calibrated for the flambda `-O3` build and is a few
words over under the non-flambda Nix compiler.

`.github/workflows/ci.yml` runs the lift gate, the semantics gate, and the
unit check on every push.  The gates are strict: `out_rmw_oob` currently
fails the semantics gate and must be fixed rather than allowed through.
