module Var = Soteria.Symex.Var

let vars_of_cv (cv : Core_value.t) : Var.Hashset.t =
  Core_value.iter_vars cv |> Iter.map fst |> Var.Hashset.of_iter

let vars_of_cvs (cvs : Core_value.t Iter.t) : Var.Hashset.t =
  Iter.flat_map Core_value.iter_vars cvs |> Iter.map fst |> Var.Hashset.of_iter

(* [Hashset.inter] is not exposed on mainline soteria; count the intersection
   directly. *)
let inter_count l r =
  let count = ref 0 in
  Var.Hashset.iter (fun v -> if Var.Hashset.mem r v then incr count) l;
  !count

(** We define the following heuristics for deciding what to unfold when
    recovering from a verification failure:
    - Each matching in-parameter is worth 2 points
    - Each matching out-parameter is worth 1 point *)
let recovery_heuristics (relevant_values : Core_value.t Iter.t) :
    Core_value.t Predicates.unfold_heuristics =
 fun ins outs ->
  let relevant_vars = vars_of_cvs relevant_values in
  let ins_vars = vars_of_cvs (Iter.of_list ins) in
  let outs_vars = vars_of_cvs (Iter.of_list outs) in
  let ins_score = inter_count relevant_vars ins_vars in
  let outs_score = inter_count relevant_vars outs_vars in
  let score = (ins_score * 2) + outs_score in
  if score > 0 then Some score else None

(** On an explicit if/else in the language, we try and unfold a predicate that
    has matching in-parameters. *)
let if_else_heuristics (guard : Core_value.t) :
    Core_value.t Predicates.unfold_heuristics =
 fun ins _ ->
  let relevant_vars = vars_of_cv guard in
  let ins_vars = vars_of_cvs (Iter.of_list ins) in
  let ins_score = inter_count relevant_vars ins_vars in
  if ins_score > 0 then Some ins_score else None
