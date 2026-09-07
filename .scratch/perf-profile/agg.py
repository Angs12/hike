#!/usr/bin/env python3
"""Aggregate perf script dumps into phase buckets.

perf script chain order: leaf frame first, callers below.

Primary phase = the FIRST chain frame (scanning up from the leaf) matching
an orchestration anchor; anchors are checked per-frame in priority order.
Chains with no hike anchor: frontend/lift anchors (anywhere), else BAP
glue (outermost), else a runtime class (leaf-first).
"""
import sys
import re
from collections import Counter

# orchestration anchors, per-frame priority order
PHASES = [
    ("refine_walk", re.compile(
        r"refine_edge|refine_chain|refine_cast|constrain_def_chain|"
        r"constrain_cell|Cbat_contextual_fixpoint|def_constraints|"
        r"apply_operand_constraint|operand_constraint|edge_views|"
        r"route_phi|reverse_def_walk|compute_val|"
        r"anon_fn\[cbat_vsa\.pp\.ml:(1357|597),")),
    ("extract", re.compile(
        r"Cbat_vsa\.extract_|Cbat_vsa\.classify|Cbat_vsa\.bounds_of|"
        r"Cbat_vsa\.equal_kind|Cbat_vsa\.k_range|Cbat_vsa\.offsets")),
    ("stack_model", re.compile(r"Hike[._]?Hike_stack_model\.")),
    ("vla_detect", re.compile(r"detect_dynamic_alloc")),
    ("stl_pass", re.compile(r"Hike[._]?Hike_stack_to_locals")),
    ("dce_pass", re.compile(r"Hike[._]?Hike_dce")),
    ("emit", re.compile(r"Hike[._]?Bil2llvm")),
    ("filter", re.compile(
        r"Hike[._]?Hike_model_clean|Hike[._]?Convutils|Hike[._]?Hike_kb|Hike[._]?Hike_diag")),
    ("fixpoint", re.compile(
        r"static_graph_vsa|stabilize_worklist|process_vertex|"
        r"denote_block_with_stores|denote_defs|denote_def|denote_jump|"
        r"denote_exp|denote_imm|denote_binop|Cbat_landmarks|"
        r"selective_widen|widen_join|Cbat_runctx|Transfer_memo|Walk_memo|"
        r"Cbat_memo|Cbat_wto|compute_need|collect_heads|"
        r"frame_of_state|init_sol|mem_call|call_abstraction|"
        r"anon_fn\[cbat_vsa\.pp\.ml:(2316|2303|277),")),
    ("producer_setup", re.compile(
        r"anon_fn\[cbat_vsa\.pp\.ml:(2107|2115|1891),")),
    ("producer_glue", re.compile(
        r"Hike[._]?Hike_vsa\.offsets_of_sub|has_mem_ops")),
    ("pass_driver", re.compile(r"^Hike\.")),
    ("frontend_lift", re.compile(
        r"Bap_disasm|Bap_image|Bap_bil_lifter|Bap_x86|Bap_frontend|"
        r"Frontend_parser|Bap_primus|Primus_lisp")),
    ("dynlink", re.compile(r"caml_natdynlink|Dynlink_common")),
]

BAP_GLUE = re.compile(
    r"Bap_main|Bap_pass|Bap_future|Bap_knowledge|Cmdliner|caml_program$|Graphs__")

RUNTIME = [
    ("gmp_zahlen", re.compile(r"__gmpn_|ml_z_|Z\.|^GMP")),
    ("gc", re.compile(r"do_some_marking|minor_gc|major_gc|oldify|sweep|"
                      r"caml_alloc|caml_garbage|intern_alloc|pool_")),
    ("ocaml_runtime", re.compile(r"^caml_")),
    ("sys", re.compile(r"^\[kernel|^/usr/lib|^/lib|^/home/tovpr/scratch")),
]

# abstract-domain leaf modules (secondary annotation)
DOMAIN = re.compile(
    r"Cbat_clp|Cbat_fin_set|Cbat_interval_tree|Cbat_map_lattice|"
    r"Cbat_word_ops|Cbat_ai_memmap|Cbat_ai_representation|Cbat_wordset")


def frame(line):
    m = re.match(r"^\s*[0-9a-f]+\s+(\S+)\s+\((\S+)\)\s*$", line)
    if not m:
        return None
    sym, dso = m.group(1), m.group(2)
    if sym.startswith("["):
        sym = dso
    return sym, dso


def classify(chain):
    for sym, dso in chain:
        for phase, rx in PHASES:
            if rx.search(sym):
                return phase
    for sym, dso in chain:
        if FRONTEND_ANY.search(sym) or FRONTEND_ANY.search(dso):
            return "frontend"
    for sym, dso in reversed(chain):
        if BAP_GLUE.search(sym):
            return "bap_glue"
    if any(DOMAIN.search(s) for s, _ in chain):
        return "ai_domain"
    for sym, dso in chain:
        for cls, rx in RUNTIME:
            if rx.search(sym) or rx.search(dso):
                return cls
    return "other"


FRONTEND_ANY = PHASES  # placeholder replaced below
FRONTEND_ANY = re.compile(
    r"Bap_disasm|Bap_image|Bap_bil_lifter|Bap_x86|Bap_frontend|"
    r"Frontend_parser|Bap_primus|Primus_lisp")


def main():
    files = sys.argv[1:] or ["-"]
    phases = Counter()
    leaves = Counter()
    domain = Counter()   # per-phase count of chains containing a domain frame
    total = 0
    for fn in files:
        fh = sys.stdin if fn == "-" else open(fn, errors="replace")
        chain = []
        state = {"total": 0}

        def flush():
            if chain:
                total = state["total"] = state["total"] + 1
                ph = classify(chain)
                phases[ph] += 1
                leaves[(ph, chain[0][0])] += 1
                if any(DOMAIN.search(s) for s, _ in chain):
                    domain[ph] += 1
                chain.clear()

        for line in fh:
            if not line.strip():
                flush()
                continue
            if re.match(r"^\S+\s+\d+(?:/\d+)?\s+[\d.]+:", line):
                flush()
                continue
            fr = frame(line)
            if fr:
                chain.append(fr)
        flush()
        if fn != "-":
            fh.close()

    total = state["total"]
    print(f"samples\t{total}")
    for ph, n in phases.most_common():
        d = domain.get(ph, 0)
        print(f"PHASE\t{ph}\t{n}\t{100.0 * n / max(total, 1):.1f}%\t"
              f"domain_hits={d}")
    print("--- top leaves per phase ---")
    byph = {}
    for (ph, leaf), n in leaves.items():
        byph.setdefault(ph, Counter())[leaf] += n
    for ph in sorted(byph, key=lambda p: -phases.get(p, 0)):
        for leaf, n in byph[ph].most_common(10):
            print(f"LEAF\t{ph}\t{n}\t{100.0 * n / max(total, 1):5.2f}%\t{leaf[:120]}")


if __name__ == "__main__":
    main()
