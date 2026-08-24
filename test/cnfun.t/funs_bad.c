/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons { u32 head, datatype seq tail }
}

function [rec] (u32) length (datatype seq l) {
  match l {
    Seq_Nil {} => { 0u32 }
    Seq_Cons { head: _, tail: t } => { 1u32 + length(t) }
  }
}
@*/

void length_wrong(void)
/*@ requires let s = Seq_Cons { head: 7u32, tail: Seq_Nil {} };
    ensures length(s) == 2u32;
@*/
{
  /*@ unfold length(Seq_Cons { head: 7u32, tail: Seq_Nil {} }); @*/
  /*@ unfold length(Seq_Nil {}); @*/
}
