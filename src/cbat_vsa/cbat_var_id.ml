(* Program-wide variable ids: the analysis interns every variable it
   meets; the environments key by the id, so their maps and sets compare
   ints, never variable identifiers.  Ids are stable for the process;
   environments are never persisted. *)

open Bap.Std

let ids : (Var.t, int) Core.Hashtbl.t = Core.Hashtbl.create (module Var)
let vars : var option array ref = ref (Base.Array.create ~len:256 None)
let bases : int array ref = ref (Base.Array.create ~len:256 (-1))
let virtuals : bool array ref = ref (Base.Array.create ~len:256 false)
let next = ref 0

let grow (i : int) : unit =
  if i >= Base.Array.length !vars then begin
    let n = Stdlib.max (2 * Base.Array.length !vars) (i + 1) in
    let resize src default =
      let dst = Base.Array.create ~len:n default in
      Base.Array.blit ~src ~src_pos:0 ~dst ~dst_pos:0
        ~len:(Base.Array.length src);
      dst
    in
    vars := resize !vars None;
    bases := resize !bases (-1);
    virtuals := resize !virtuals false
  end

let rec intern (v : var) : int =
  match Core.Hashtbl.find ids v with
  | Some i -> i
  | None ->
    let i = !next in
    incr next;
    grow i;
    Core.Hashtbl.set ids ~key:v ~data:i;
    (!vars).(i) <- Some v;
    (!virtuals).(i) <- Var.is_virtual v;
    (* The base's id serves the keep/need tests; a base var is itself. *)
    (!bases).(i) <- intern (Var.base v);
    i

let find (v : var) : int option = Core.Hashtbl.find ids v
let var_of (i : int) : var = Core.Option.value_exn (!vars).(i)
let base_of (i : int) : int = (!bases).(i)
let is_virtual (i : int) : bool = (!virtuals).(i)

let reset () : unit =
  Core.Hashtbl.clear ids;
  next := 0;
  vars := Base.Array.create ~len:256 None;
  bases := Base.Array.create ~len:256 (-1);
  virtuals := Base.Array.create ~len:256 false

let intern_set (vs : Var.Set.t) : Core.Int.Set.t =
  Core.Set.fold vs ~init:(Core.Set.empty (module Core.Int))
    ~f:(fun acc v -> Core.Set.add acc (intern v))
