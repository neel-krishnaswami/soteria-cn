(* Vendored from soteria-tools/soteria soteria-c/lib (mainline 4e9182b; ctree_block/state_variants/csymex/symbol_std/layout from cn-main-merge 7b89176). *)
module Freeable0 = Freeable
open Csymex
module Freeable_ctree_block = Freeable (Ctree_block)
include With_origin (Freeable_ctree_block)

let pp_pretty ft t =
  pp' ~inner:(Freeable_ctree_block.pp' ~inner:Ctree_block.pp_pretty) ft t

let is_freed (t : ('a Freeable0.freeable, 'b) with_info) =
  [%matches? Freed] t.node

(* Freed, or alive but owning no bytes (its ownership was consumed, e.g. by a
   loop invariant): either way the block holds no resource. *)
let owns_nothing (t : (Ctree_block.t Freeable0.freeable, 'b) with_info) =
  match t.node with
  | Freeable0.Freed -> true
  | Freeable0.Alive ctb -> Ctree_block.owns_nothing ctb

let alloc ?loc ~zeroed size =
  {
    node = Freeable0.Alive (Ctree_block.alloc ~zeroed size);
    info = loc;
  }

let free () = wrap (Freeable_ctree_block.free ())
