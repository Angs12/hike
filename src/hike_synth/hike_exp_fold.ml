(* A post-order fold over an exp: [fold f e] computes each node's value
   from its children's, through BAP's visitor — never hand-rolled
   structural recursion.  [f] is the single-node dispatch; it reads a
   child's already-computed value through the passed lookup. *)

open Bap.Std

let fold (type r) (f : exp -> (exp -> r) -> r) (e : exp) : r =
  let tbl = ref Exp.Map.empty in
  let vis =
    object
      inherit [ unit ] Exp.visitor
      method! leave_exp e () =
        let child c = Core.Map.find_exn !tbl c in
        tbl := Core.Map.set !tbl ~key:e ~data:(f e child)
    end
  in
  vis#visit_exp e ();
  Core.Map.find_exn !tbl e
