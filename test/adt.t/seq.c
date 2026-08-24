struct sll {
  unsigned int data;
  struct sll* next;
};

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons { u32 head, datatype seq tail }
}

predicate [rec] (datatype seq) SLLseq (pointer p) {
  if (is_null(p)) {
    return Seq_Nil {};
  } else {
    take H = RW<struct sll>(p);
    take T = SLLseq(H.next);
    return Seq_Cons { head: H.data, tail: T };
  }
}
@*/

void constructors_work(void)
/*@ requires let s = Seq_Cons { head: 42u32, tail: Seq_Nil {} };
    ensures (match s { Seq_Nil {} => { 21u32 } Seq_Cons { head: h, tail: _ } => { h } }) == 42u32;
@*/
{
}

unsigned int hd_or_zero(struct sll *l)
/*@ requires take L = SLLseq(l);
    ensures take L_post = SLLseq(l);
            L_post == L;
            return == (match L { Seq_Nil {} => { 0u32 } Seq_Cons { head: h, tail: _ } => { h } });
@*/
{
  if (l == 0) {
    return 0;
  }
  return l->data;
}
