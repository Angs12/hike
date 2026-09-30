(* The def-carried KB value slots: the producer stamps each def's
   value, the emitter reads the tags off the term.  Each slot declares
   what it carries; the domain/property/getter/spelling lives once in
   Hike_def_slot.  The registrations live here, beside the readers and
   stampers -- not in the pure stack model. *)

open Bap.Std
open Bap_core_theory
open! Core
module Tag = Hike_stack_model.Tag
type sec_tag = Hike_stack_model.sec_tag

(* Per-def tags ride the def's value: the producer stamps each def, the
   emitter reads the tags off the term. *)

module KB = Bap_knowledge.Knowledge
module D = Hike_def_slot

(* The census observer: a no-op outside the debug build. *)
let bump : string -> unit =
#ifdef VSA_DEBUG
  Cbat_vsa.Cbat_kb_census.bump
#else
  fun _ -> ()
#endif

let bool_inspect (b : bool) : Sexp.t = Sexp.Atom (string_of_bool b)

(* The def is a runtime-sized SP decrement and emits a real runtime-sized
   alloca; the storage fact rides the def's value beside the kind. *)
let def_dyn_alloc : bool D.t =
  D.flat ~name:"hike-dyn-alloc" ~empty:false ~equal:Bool.equal
    ~inspect:bool_inspect ~get_bump:"dyn_alloc.get" ~put_bump:"dyn_alloc.put"
    ~bump

let def_dyn_alloc_slot = D.slot def_dyn_alloc
let def_is_dyn_alloc (d : def term) : bool = D.get def_dyn_alloc d

(* The def's address is a rip-relative constant; the emitter re-renders it
   through the section owner. *)
let def_is_rip_relative (d : def term) : bool =
#ifdef VSA_DEBUG
  let () = Cbat_vsa.Cbat_kb_census.bump "rip_relative_addr.get" in
#endif
  KB.Value.get rip_relative_addr (Def.value d)

(* The def computes an address value at/above the entry line; its emitted
   integer re-bases to the hike_window parameter. *)
let def_window_value : bool D.t =
  D.flat ~name:"hike-window-value" ~empty:false ~equal:Bool.equal
    ~inspect:bool_inspect ~get_bump:"window_value.get"
    ~put_bump:"window_value.put" ~bump

let def_window_value_slot = D.slot def_window_value
let def_is_window_value (d : def term) : bool = D.get def_window_value d

(* The def's value is a bounded stack or VLA address, so the emitter's
   ptr discipline emits it as a pointer.  Computed pre-SSA (where the
   denotation resolves) by [hike_types]; rides the def's value. *)
let def_ptr_kind_d : bool D.t =
  D.flat ~name:"hike-ptr-kind" ~empty:false ~equal:Bool.equal
    ~inspect:bool_inspect ~get_bump:"ptr_kind.get" ~put_bump:"ptr_kind.put"
    ~bump

let def_ptr_kind_slot = D.slot def_ptr_kind_d
let def_ptr_kind (d : def term) : bool = D.get def_ptr_kind_d d

(* One map applies [stamp] to every def whose tid is in [tids] — the
   slots' shared stamper. *)
let stamp_tids ~(tids : Tid.Set.t) ~stamp (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          if Core.Set.mem tids (Term.tid d) then stamp d else d))

let stamp_window_values ~(window_values : Tid.Set.t)
    (sub : sub term) : sub term =
  stamp_tids ~tids:window_values
    sub ~stamp:(fun d -> D.put def_window_value true d)

(* Stamps the dynamic-allocation fact onto the event defs. *)
let stamp_dyn_allocs ~(dynamic_alloc_tids : Tid.Set.t)
    (sub : sub term) : sub term =
  stamp_tids ~tids:dynamic_alloc_tids
    sub ~stamp:(fun d -> D.put def_dyn_alloc true d)

let stamp_ptr_kinds ~(ptr_tids : Tid.Set.t) (sub : sub term) : sub term =
  stamp_tids ~tids:ptr_tids sub ~stamp:(fun d -> D.put def_ptr_kind_d true d)

(* The storage a ptr-kind value lives in: the region/residue alloca, the
   caller frame base, or a VLA.  Stamped by [hike_types] beside the
   kind; the emitter's pointer arguments read it. *)
type KB.conflict += Ptr_storage_conflict

let () =
  KB.Conflict.register_printer (function
    | Ptr_storage_conflict ->
        Some
          "hike: ptr-storage conflict: two different storages were stamped for one def"
    | _ -> None)

let def_ptr_storage_d : Hike_stack_model.ptr_storage option D.t =
  D.optional ~name:"hike-ptr-storage"
    ~inspect:(fun _ -> Sexp.Atom "hike:ptr-storage")
    ~join:(fun a b ->
      if Hike_stack_model.equal_ptr_storage a b then Ok a
      else Error Ptr_storage_conflict)
    ~equal:Hike_stack_model.equal_ptr_storage
    ~get_bump:"ptr_storage.get" ~put_bump:"ptr_storage.put" ~bump

let def_ptr_storage_slot = D.slot def_ptr_storage_d
let def_ptr_storage (d : def term) : Hike_stack_model.ptr_storage option =
  D.get def_ptr_storage_d d

let stamp_ptr_storages ~(storages : Hike_stack_model.ptr_storage Tid.Map.t)
    (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          match Core.Map.find storages (Term.tid d) with
          | Some s -> D.put def_ptr_storage_d (Some s) d
          | None -> d))

(* The storage of the address a def accesses (or computes) — stamped by
   the attribution's rewrite, so the emitter materializes every stack
   address in its own alloca. *)
let stamp_ptr_storage (s : Hike_stack_model.ptr_storage) (d : def term) :
    def term =
  D.put def_ptr_storage_d (Some s) d

(* The section tag rides the def's value: the producer stamps it, the
   emitter's dispatch reads it off the term. *)

type KB.conflict += Sec_tag_conflict

let () =
  KB.Conflict.register_printer (function
    | Sec_tag_conflict ->
        Some
          "hike: section-tag conflict: two different attributions were stamped for one def"
    | _ -> None)

let sec_tag_d : sec_tag option D.t =
  D.optional ~name:"hike-section-tag"
    ~inspect:(fun _ -> Sexp.Atom "hike:section-tag")
    ~join:(fun a b -> if Tag.equal a b then Ok a else Error Sec_tag_conflict)
    ~equal:(fun a b ->
      bump "domain.sec.equal";
      Tag.equal a b)
    ~get_bump:"sec_tag.get" ~put_bump:"sec_tag.put" ~bump

let sec_tag_slot = D.slot sec_tag_d
let sec_tag (d : def term) : sec_tag option = D.get sec_tag_d d

let set_sec_tag (t : sec_tag) (d : def term) : def term =
  D.put sec_tag_d (Some t) d
