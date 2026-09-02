(* hike_diag.ml — THE sanctioned production output channel.

   Principle #6 (AGENTS.md, "Debug instrumentation lives in the debug build
   ONLY") as of 2026-09-02 reads STRICTLY: instrumentation is NOT COMPILED
   INTO the production binary. Production code may emit exactly two kinds
   of output, both FIXED (never runtime-switchable):

   - the permanent, operator-facing `hike:` diagnostics below (the family
     scripts/run_corpus.sh greps for: "hike: (guarded|undef-read):");
   - legitimate error raising (exceptions, KB conflicts).

   Everything a developer adds to understand code — tracing, per-sub
   progress, value dumps, profiling — is DEBUG instrumentation: it goes
   behind cppo's `#ifdef VSA_DEBUG` in the .ml source and is compiled out
   of every non-vsa-debug build (see the (preprocess ...) stanza in dune).
   NEVER a `Sys.getenv` gate: any runtime-variable behavior is debug
   (Q1), and env reads are banned from src/ BY CONSTRUCTION (the
   check-instrumentation rule in dune blocks the build on them).

   The channel is deliberately tiny: one warning path (eprintf to stderr,
   the format scripts grep) + one BAP-log path. Sites that used to print
   BOTH now print ONCE (the cbat_vsa not_implemented double-report is
   gone). Do not add anything here without a battery-visible reason. *)

(* One production warning to stderr. The [hike:] prefix is the contract:
   run_corpus.sh counts these as "surviving diagnostics", so the prefix is
   load-bearing — never emit an operator-facing warning without it. *)
let warn fmt =
  Printf.ksprintf
    (fun s -> Printf.eprintf "hike: %s\n" s)
    fmt

(* A deduplicated warning: warns once per [key] (the per-sub guarded
   warnings fire per-def; the operator needs them once per sub). *)
let warn_once ~(tbl : unit -> bool ref) ~(set : unit -> unit) key fmt =
  Printf.ksprintf
    (fun s ->
      let seen = tbl () in
      if not !seen then begin
        Printf.eprintf "hike: %s\n" s;
        set ();
        seen := true
      end)
    fmt
