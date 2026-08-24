open Soteria.Soteria_std
module Sym = Soteria_c_vendor.Symbol_std
module Csymex = Soteria_c_vendor.Csymex

module P = struct
  module A =
    Monad.StateT_base
      (struct
        type t = Subst.t
      end)
      (State.SM)

  include A
  include Monad.Extend (A)

  let lift_state s = lift s
  let lift s = lift (State.SM.lift s)

  let run_with_subst ~subst (f : 'a t) : ('a * Subst.t) State.SM.t =
    run_with_state ~state:subst f

  (* State.SM.branches : (unit -> 'a SM.t) list -> 'a SM.t *)
  (* (unit -> subst -> ('a * subst) SM.t) list ->
    subst -> ('a * subst) SM.t *)

  let branches (brs : (unit -> 'a t) list) : 'a t =
   fun subst -> State.SM.branches (List.map (fun f -> fun () -> f () subst) brs)

  module Subst = struct
    let eval_annot annot =
      let open Syntax in
      let* subst = get_state () in
      lift @@ Subst.eval_annot subst annot

    let add (sym : Sym.t) (v : Core_value.t) : unit t =
     fun subst ->
      let subst = Subst.add sym v subst in
      State.SM.return ((), subst)
  end

  let with_loc ~loc (f : unit -> 'a t) : 'a t =
   fun subst state -> Csymex.with_loc ~loc (f () subst state)

  module Syntax = struct
    include Syntax

    let ( let*^ ) x f = bind f (lift x)
  end
end

include P

module With_syntax = struct
  include P
  include P.Syntax
end
