(* The def-carried KB value slots: the producer stamps each def's
   value, the emitter reads the tags off the term.  The slot
   registrations live here, beside the readers and stampers -- not in
   the pure stack model. *)

open Bap.Std
open Bap_core_theory
module Tag = Hike_stack_model.Tag
type sec_tag = Hike_stack_model.sec_tag

(* Per-def tags ride the def's value: the producer stamps each def, the
   emitter reads the tags off the term. *)

module KB = Bap_knowledge.Knowledge

(* The def is a runtime-sized SP decrement and emits a real runtime-sized
   alloca; the storage fact rides the def's value beside the kind. *)
let def_dyn_alloc_slot : (Theory.Value.cls, bool) KB.slot =
  let bool_domain =
    KB.Domain.flat
      ~inspect:(fun b -> Base.Sexp.Atom (string_of_bool b))
      ~equal:Bool.equal ~empty:false "hike:dyn-alloc"
  in
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-dyn-alloc"
    bool_domain

let def_is_dyn_alloc (d : def term) : bool =
#ifdef VSA_DEBUG
  let () = Cbat_vsa.Cbat_kb_census.bump "dyn_alloc.get" in
#endif
  KB.Value.get def_dyn_alloc_slot (Def.value d)

(* The def's address is a rip-relative constant; the emitter re-renders it
   through the section owner. *)
let def_is_rip_relative (d : def term) : bool =
#ifdef VSA_DEBUG
  let () = Cbat_vsa.Cbat_kb_census.bump "rip_relative_addr.get" in
#endif
  KB.Value.get rip_relative_addr (Def.value d)

(* The def computes an address value at/above the entry line; its emitted
   integer re-bases to the hike_window parameter. *)
let def_window_value_slot : (Theory.Value.cls, bool) KB.slot =
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-window-value"
    (KB.Domain.flat
       ~inspect:(fun b -> Base.Sexp.Atom (string_of_bool b))
       ~equal:Bool.equal ~empty:false "hike:window-value")

let def_is_window_value (d : def term) : bool =
#ifdef VSA_DEBUG
  let () = Cbat_vsa.Cbat_kb_census.bump "window_value.get" in
#endif
  KB.Value.get def_window_value_slot (Def.value d)

(* The def's value is a bounded stack or VLA address, so the emitter's
   ptr discipline emits it as a pointer.  Computed pre-SSA (where the
   denotation resolves) by [hike_types]; rides the def's value. *)
let def_ptr_kind_slot : (Theory.Value.cls, bool) KB.slot =
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-ptr-kind"
    (KB.Domain.flat
       ~inspect:(fun b -> Base.Sexp.Atom (string_of_bool b))
       ~equal:Bool.equal ~empty:false "hike:ptr-kind")

let def_ptr_kind (d : def term) : bool =
  KB.Value.get def_ptr_kind_slot (Def.value d)

(* One map applies [stamp] to every def whose tid is in [tids] — the
   two bool slots' shared stamper. *)
let stamp_tids ~(tids : Tid.Set.t) ~stamp (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          if Core.Set.mem tids (Term.tid d) then stamp d else d))

let stamp_window_values ~(window_values : Tid.Set.t)
    (sub : sub term) : sub term =
  stamp_tids ~tids:window_values sub ~stamp:(fun d ->
#ifdef VSA_DEBUG
      let () = Cbat_vsa.Cbat_kb_census.bump "window_value.put" in
#endif
      Def.with_value d
        (KB.Value.put def_window_value_slot (Def.value d) true))

(* Stamps the dynamic-allocation fact onto the event defs. *)
let stamp_dyn_allocs ~(dynamic_alloc_tids : Tid.Set.t)
    (sub : sub term) : sub term =
  stamp_tids ~tids:dynamic_alloc_tids sub ~stamp:(fun d ->
#ifdef VSA_DEBUG
      let () = Cbat_vsa.Cbat_kb_census.bump "dyn_alloc.put" in
#endif
      Def.with_value d
        (KB.Value.put def_dyn_alloc_slot (Def.value d) true))

let stamp_ptr_kinds ~(ptr_tids : Tid.Set.t) (sub : sub term) : sub term =
  stamp_tids ~tids:ptr_tids sub ~stamp:(fun d ->
#ifdef VSA_DEBUG
      let () = Cbat_vsa.Cbat_kb_census.bump "ptr_kind.put" in
#endif
      Def.with_value d
        (KB.Value.put def_ptr_kind_slot (Def.value d) true))

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

let def_ptr_storage_slot :
    (Theory.Value.cls, Hike_stack_model.ptr_storage option) KB.slot =
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-ptr-storage"
    (KB.Domain.optional
       ~inspect:(fun _ -> Base.Sexp.Atom "hike:ptr-storage")
       ~join:(fun a b ->
         if Hike_stack_model.equal_ptr_storage a b then Ok a
         else Error Ptr_storage_conflict)
       ~equal:Hike_stack_model.equal_ptr_storage
       "hike:ptr-storage")

let def_ptr_storage (d : def term) : Hike_stack_model.ptr_storage option =
  KB.Value.get def_ptr_storage_slot (Def.value d)

let stamp_ptr_storages ~(storages : Hike_stack_model.ptr_storage Tid.Map.t)
    (sub : sub term) : sub term =
  Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:(fun d ->
          match Core.Map.find storages (Term.tid d) with
          | Some s ->
              Def.with_value d
                (KB.Value.put def_ptr_storage_slot (Def.value d) (Some s))
          | None -> d))

(* The storage of the address a def accesses (or computes) — stamped by
   the attribution's rewrite, so the emitter materializes every stack
   address in its own alloca. *)
let stamp_ptr_storage (s : Hike_stack_model.ptr_storage) (d : def term) :
    def term =
  Def.with_value d
    (KB.Value.put def_ptr_storage_slot (Def.value d) (Some s))

(* The section tag rides the def's value: the producer stamps it, the
   emitter's dispatch reads it off the term. *)

type KB.conflict += Sec_tag_conflict

let () =
  KB.Conflict.register_printer (function
    | Sec_tag_conflict ->
        Some
          "hike: section-tag conflict: two different attributions were stamped for one def"
    | _ -> None)

let sec_tag_domain : sec_tag option KB.Domain.t =
  KB.Domain.optional
    ~inspect:(fun _ -> Base.Sexp.Atom "hike:section-tag")
    ~join:(fun a b -> if Tag.equal a b then Ok a else Error Sec_tag_conflict)
    ~equal:(fun a b ->
#ifdef VSA_DEBUG
      let () = Cbat_vsa.Cbat_kb_census.bump "domain.sec.equal" in
#endif
      Tag.equal a b)
    "hike:section-tag"

let sec_tag_slot : (Theory.Value.cls, sec_tag option) KB.slot =
  KB.Class.property ~package:"hike" Theory.Value.cls "hike-section-tag"
    sec_tag_domain

let sec_tag (d : def term) : sec_tag option =
#ifdef VSA_DEBUG
  let () = Cbat_vsa.Cbat_kb_census.bump "sec_tag.get" in
#endif
  KB.Value.get sec_tag_slot (Def.value d)

let set_sec_tag (t : sec_tag) (d : def term) : def term =
#ifdef VSA_DEBUG
  let () = Cbat_vsa.Cbat_kb_census.bump "sec_tag.put" in
#endif
  Def.with_value d (KB.Value.put sec_tag_slot (Def.value d) (Some t))
