# hike — the complete architecture map (Mermaid)

One plugin, one pipeline, one mechanism. Generated 2026-09-11 from the
landed record (AGENTS.md validation blocks, ADRs 0001–0009, the
typed-model program's ticket verdicts). Read top-to-bottom: the
pipeline, the producer (VSA) internals, the stack model, the emitter
dispatch, the decision ledger, and the measured-gains ledger.

## 1. The pass pipeline (the plugin's spine)

```mermaid
flowchart TB
    BIN["x86-64 PIE ELF binary<br/>(corpus: gcc -O0 / -O2, -fno-stack-protector)"]
    BAP["BAP frontend<br/>(lifts to BIR: subs / blocks / defs / BIL exps)"]

    subgraph P1["pass 1 — hike-filter (FIRST in chain)"]
        F1["named exclusions<br/>stub / extern / intrinsic filter<br/>intrinsic-callers filter<br/>symbol-table check"]
    end

    subgraph P2["pass 2 — hike-vsa (the PRODUCER — computes every fact once)"]
        FIX["Bourdoncle WTO fixpoint<br/>(static_graph_vsa)"]
        EXT["Cbat_extraction.extract<br/>(the M6 classification walk)"]
        SM["Hike_stack_model<br/>(frame_dims, window_dims,<br/>regions_of_sub, split_plan,<br/>promotion facts)"]
    end

    subgraph P3["pass 3 — hike-stack-to-locals (ONE registration, two rewrites)"]
        STL["(a) region merge + tag<br/>(VSA calculates, STL only merges)"]
        DCE["(b) Hike.Dce<br/>epilogue replacement +<br/>never-used def sweep to fixpoint"]
    end

    subgraph P4["pass 4 — hike-convlir (the EMITTER)"]
        SIG["signature collection<br/>(promoted signatures,<br/>hike_window, thunks)"]
        BODY["body emission<br/>(bil2llvm* via the ONE seam<br/>Bil2llvm.emit_program)"]
    end

    OUT["LLVM IR module<br/>(--hike-output-file out.ll)<br/>37-bin corpus: emission rc=0"]

    BIN --> BAP --> P1 --> P2 --> P3 --> P4 --> OUT
    FIX --> EXT --> SM
    STL --> DCE
    SIG --> BODY
    P2 -. "vsa_info record = the ONLY carrier<br/>of stack-access-ness (KB: Hike_kb.info_of_sub)" .-> P3
    P2 -. "the record is authoritative —<br/>consumers never re-derive" .-> P4
```

## 2. The producer's internals (the ONE mechanism)

```mermaid
flowchart TB
    SEED["entry seed: RSP's word =<br/>the symbolic stack segment<br/>StackOff in [2^62, 2^62 + 8MiB]<br/>(T3: arithmetic propagates the symbol;<br/>bitwise / compares go TOP-unknown —<br/>the L1 class structurally impossible)"]

    subgraph FIXP["the fixpoint (per sub)"]
        DD["denote_defs: the block's defs folded<br/>SEQUENTIALLY (intra-block def-use exact)"]
        PRED["per-predecessor transfer:<br/>the pred's whole def fold applied<br/>to the pred's entry state, then join"]
        WIDE["warmed-head widening (visits > 10):<br/>landmark-directed (Simon and King port)<br/>lm_calc_steps -> selective_widen_extrapolate<br/>Zero -> join, Inf -> plain widen"]
        DEEP["the deep backward walk, INLINE at every<br/>conditional jump: producer subtraction<br/>cstr' = cstr and post(v),<br/>trace-exact cell meets"]
        DD --> PRED --> WIDE
        PRED --> DEEP
    end

    JUMPC["THE JUMP COMPILER (the hike-jump BIR pass,<br/>FIRST in the analysis chain — T13): every<br/>compilable conditional jump is REWRITTEN to the<br/>simplest equivalent value comparison BEFORE the<br/>analysis runs; the walk consumes plain comparisons<br/>where the rewrite fired — comparison_constraint's<br/>rows serve both edges; the landmark machinery<br/>and the residual identity path are unchanged"]
    JUMPC --> DEEP

    PRED2["is_stack_access addr st =<br/>the ONE predicate:<br/>the address's DENOTATION is a<br/>stack-symbolic set inside the segment<br/>(T3c: the escape and every second<br/>channel are DELETED)"]

    subgraph TAGS["the tag product (vsa_info — facts, not flags)"]
        R["Range lo hi<br/>(bounded interval)"]
        I["Infinite<br/>(widened bounds)"]
        U["Unbounded<br/>(TOP — may name this frame)"]
        D["Dead<br/>(BOTTOM path — warned poison)"]
        V["VLA<br/>(dynamic allocation)"]
    end

    CS["caller_split: entirely-above-entry -> Caller;<br/>two-sided/wrapped -> Mixed<br/>(Mixed PRODUCTION arms die in T9)"]

    PROM["T4 promotion facts:<br/>prom_slots / prom_arity<br/>prom_sites (slot index -> storing def)<br/>prom_resolved (indirect targets)<br/>prom_window / prom_retaddr"]

    SPLIT["regions_of_sub + split_plan:<br/>connected components of the<br/>interval-overlap graph; storage class<br/>Static / Frame / Dynamic / Dead<br/>(purely geometric post-T3c)"]

    SEED --> FIXP --> JUMPC
    SEED --> FIXP --> PRED2 --> TAGS
    PRED2 --> CS --> PROM
    TAGS --> SPLIT
    DEEP -. "constraints flow backward through<br/>guards and loads; stores join in T5" .-> WIDE
```

## 3. The emitter's dispatch (complete rules per tag kind)

```mermaid
flowchart TB
    DEF["a memory def reaches emission<br/>(mem_access: dispatch on the tag kind —<br/>total, no arms that refuse)"]

    RI["Range / Infinite + license<br/>-> THE uniform rule:<br/>gep storage, val - anchor + anchor_idx<br/>(T1: the license is the producer's<br/>frame-residency proof — the T1 lesson:<br/>wrapping an unproven address tells LLVM<br/>the wrong underlying object and<br/>opt deletes live stores)"]
    UN["Unbounded<br/>-> warned + plain materialization<br/>(identity, never bottom)"]
    VLA["VLA<br/>-> a REAL dynamic alloca<br/>(alloca i8, i64 size)"]
    DEADD["Dead<br/>-> warned poison<br/>(never executed; loud, not silent)"]
    CALLER["Caller (incoming slot)<br/>-> the promoted parameter hike_slotN<br/>(stored at width; narrower reads truncate;<br/>WRITTEN slots demoted to the window —<br/>T4b rule 4)<br/>retaddr reads bind undef (die with ret)"]
    MIXED["Mixed (va walk)<br/>-> the two-base select<br/>select(word >= stack_0, window + off, word)<br/>(the argued complete rule; the arms die in T9)"]

    ADRI["an address INTEGER (any exp)<br/>-> create_addr_ptr:<br/>licensed -> gep into the anchor storage<br/>unlicensed -> inttoptr (the Exception Lane:<br/>foreign pointers, section/global constants —<br/>ADR 0009; inttoptr claims no basedness)"]

    RES["an indirect call<br/>-> resolve_target (the denotation of the target):<br/>singleton lifted sub -> DIRECT promoted call<br/>multi-target / foreign / TOP -> pointer call"]
    THUNK["-> lands in an INTERNAL thunk:<br/>the memory-convention twin that unpacks<br/>window memory and calls the promoted body<br/>(fn-pointer data renders to twins;<br/>internal = IPSCCP devirt + inline + GlobalDCE)"]

    SPS["the SP Slot (T4):<br/>every storage-carrying sub's entry block:<br/>sp_slot = alloca i64; SP binds to<br/>ptrtoint(frame) or region-0 base<br/>(hike_stack is ZERO in src and emissions;<br/>per-invocation anchor = reentrancy-safe)"]

    DEF --> RI
    DEF --> UN
    DEF --> VLA
    DEF --> DEADD
    DEF --> CALLER
    DEF --> MIXED
    DEF --> ADRI
    RES --> THUNK
    RI --> SPS
    CALLER --> SPS
```

## 4. The decision ledger (why the architecture is what it is)

```mermaid
flowchart LR
    ADR3["ADR 0003 + the no-gates lane:<br/>the restriction tag, the relevance pass,<br/>and every refineable gate DELETED;<br/>denote_def denotes every def"]
    ADR8["ADR 0008 sp-only:<br/>RBP is an ordinary GPR;<br/>a register's stack-ness is PROVEN,<br/>never assumed by name"]
    ADR9["ADR 0009 + tickets 03/04:<br/>the typed frame is THE model;<br/>the offset path and the<br/>--hike-stack-model parameter deleted"]
    T1r["T1: the frame-wrap LICENSE<br/>(opt-safety 31/2 -> 33/33):<br/>wrapping an unproven integer tells LLVM<br/>the wrong underlying object"]
    T3r["T3: the symbolic stack base<br/>(the segment seed; one predicate;<br/>value_env and the frame relation deleted;<br/>the uniform materialization rule)"]
    T3cr["T3c: the escape DELETED entirely<br/>(the partition reads the denotations;<br/>the -O2 pin moved 6 -> 4:<br/>fizzbuzz_safe + fptr_table flipped green)"]
    T4r["T4: the grilled convention<br/>(promotion, the SP Slot, resolved<br/>indirect calls, internal thunks,<br/>hike_window) — ahead of all four<br/>prior lifters; no precedent to lean on"]
    T4br["T4b: conversion correctness<br/>(four constructed rules, zero gates:<br/>Unknown seeding, node-served Caller lane,<br/>stored-value slot args, written-slot<br/>demotion — strict -O0 32/5 -> 37/37)"]
    T13["T13 (wire-up): THE JUMP-COMPILER PASS —<br/>the hike-jump BIR pass (FIRST in the chain)<br/>rewrites every compilable conditional jump to a<br/>value comparison ONCE, before the VSA (the<br/>sub-family + the test/and family: OF ≡ 0);<br/>decoupled, more optimizable LLVM"]
    DOCT["THE DOCTRINE (binding):<br/>NO GATES — no conditional refusals<br/>NO FALLBACKS — identity is the only fallback<br/>ONE MECHANISM — the denotation answers everything<br/>FIX THE ARCHITECTURE, NOT THE IMPLEMENTATION —<br/>the fix's diff DELETES cases<br/>CONVERSION FIRST — failures are inventoried"]

    ADR3 --> T3r
    ADR8 --> T4r
    ADR9 --> T1r --> T3r --> T3cr --> T4r --> T4br
    DOCT -.governs every lane.-> T4br
```

## 5. The measured-gains ledger (every precision/speed movement)

```mermaid
flowchart LR
    subgraph ORACLE["the primary oracles"]
        O0["-O0 strict semantics:<br/>32/32 -> 33/33 (sp_reload)<br/>-> 37/37 (T4 sources)<br/>-> 32/5 (T4 conversion reds)<br/>-> 37/37 (T4b)"]
        OPT["strict opt-safety:<br/>31/2 (the typed regression)<br/>-> 33/33 (T1)<br/>-> 37/37 (T4b)"]
        REF["the differential referee:<br/>2,861,148 checks / 0 mismatches<br/>(held through EVERY lane)"]
    end

    subgraph PIN["the -O2 red list (always deliberate)"]
        P7["7 (the four-mechanism record)"]
        P6["6 (deep_recursion flipped, lane 3)"]
        P4["4 (T3c: escape death -><br/>fizzbuzz_safe + fptr_table green)"]
        P9["9 (T4: the conversion's reds)"]
        P7B["7 (T4b: fn_escape + fn_table_disp<br/>proven flips) — each member owned:<br/>L3 x2 = T5, L1 x2, vacopy = T9,<br/>spill_many = next dig, jump_table_sw = dispatch"]
        P7 --> P6 --> P4 --> P9 --> P7B
    end

    subgraph CONV["the convergence report (-O0-lift post-opt / -O2-lift post-opt)"]
        C1["the memory-passed class:<br/>deep_chain 323/4, many_args 133/4,<br/>spill_many 134/4, nested_calls 75/4"]
        C2["T4's promotion:<br/>many_args 121->58, mixed_fp_int 136->68,<br/>variadic -O2 185->27"]
        C3["T4b: six more sources SAME/SAME<br/>(array_local, fn_escape, fn_table_disp,<br/>nested_struct, sret_big, struct_by_value)<br/>- no regressions"]
        C1 --> C2 --> C3
    end

    subgraph PREC["precision / code health"]
        PR1["inttoptr corpus-wide: 447 -> 259 (T3-era)<br/>-> ZERO in precise subs (T4b census:<br/>1,908 cell accesses all frame-GEP rooted)"]
        PR2["the 21 subs T3c honestly re-framed<br/>ALL recovered exact region counts (T4b)"]
        PR3["allocas: 185-0 structural asserts;<br/>regions split, one storage per sub"]
        PR4["code: 62.8k -> ~40k lines (2026-09 waves);<br/>T4b net +176/-94 with ~60 lines rule docs;<br/>the two-profile build (10-22 s rebuilds avoided)"]
    end
```

## 6. The validation battery (what every lane must hold)

```mermaid
flowchart LR
    B["scripts/battery.sh<br/>(the canonical driver)"]
    B --> CAN["provenance canaries:<br/>the plugin IS this tree's build;<br/>corpus_o2 is genuinely -O2<br/>(byte_copy / fizzbuzz_safe differ)"]
    B --> RT["dune runtest:<br/>failure set == the 8 pre-existing<br/>+ named inventory; referee 0"]
    B --> EM["-O0 + -O2 emission rc=0<br/>(37/37) + check_allocas"]
    B --> SEM["strict -O0 semantics<br/>+ strict opt-safety"]
    B --> PIN2["the pinned -O2 gate:<br/>the set moves only deliberately"]
    B --> CONV2["the convergence report:<br/>the movement instrument"]
```
