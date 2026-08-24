open Soteria.Soteria_std
module Sym = Soteria_c_vendor.Symbol_std
module Csymex = Soteria_c_vendor.Csymex
module Result = State.SM.Result

module C = struct
  module A = struct
    type 'a t =
      Subst.t -> ('a * Subst.t, Cn_error.with_trace, State.syn list) Result.t

    let ok x = fun subst -> Result.ok (x, subst)
    let error err = fun _subst -> State.SM.lift (Cn_error.error_with_loc err)
    let miss () = error `Missing_resource

    let bind (f : 'a -> 'b t) (m : 'a t) : 'b t =
      let open State.SM.Syntax in
      fun subst ->
        let** x, subst = m subst in
        f x subst

    let map (f : 'a -> 'b) (m : 'a t) : 'b t =
      let open State.SM.Syntax in
      fun subst ->
        let++ x, subst = m subst in
        (f x, subst)
  end

  include Monad.Extend (struct
    include A

    let return = ok
  end)

  let get_subst () : Subst.t t = fun subst -> Result.ok (subst, subst)

  let run_with_subst ~subst (m : 'a t) :
      ('a * Subst.t, Cn_error.with_trace, State.syn list) Result.t =
    m subst

  let lift (s : 'a Csymex.t) : 'a t =
   fun subst state -> Csymex.map (fun x -> (Compo_res.Ok (x, subst), state)) s

  let lift_state (s : ('a, _, _) Result.t) : 'a t =
   fun subst -> Result.map (fun x -> (x, subst)) s

  let not_impl msg = lift (Soteria_c_helpers.not_impl msg)

  module Syntax = struct
    include Syntax

    let ( let*^ ) x f = bind f (lift x)
  end

  open Syntax

  module Subst = struct
    let eval_annot annot : Core_value.t t =
      let* subst = get_subst () in
      lift @@ Subst.eval_annot subst annot

    let add (sym : Sym.t) (v : Core_value.t) : unit t =
     fun subst -> Result.ok ((), Subst.add sym v subst)
  end

  let with_loc ~loc (f : unit -> 'a t) : 'a t =
   fun state subst -> Csymex.with_loc ~loc (f () state subst)
end

module With_syntax = struct
  include C
  include Syntax
end

include C
