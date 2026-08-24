struct sll {
  unsigned int data;
  struct sll* next;
};

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons { u32 head, datatype seq tail }
}
@*/

void constructors_work(void)
/*@ requires let s = Seq_Cons { head: 42u32, tail: Seq_Nil {} };
    ensures (match s { Seq_Nil {} => { 21u32 } Seq_Cons { head: h, tail: _ } => { h } }) == 41u32;
@*/
{
}
