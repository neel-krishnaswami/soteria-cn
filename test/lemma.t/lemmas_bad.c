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

function [rec] (u32) length (datatype seq l) {
  match l {
    Seq_Nil {} => { 0u32 }
    Seq_Cons { head: _, tail: t } => { 1u32 + length(t) }
  }
}
@*/

extern struct sll *malloc_sll ();
/*@ spec malloc_sll();
    ensures take P = W<struct sll>(return);
@*/

struct sll *push_no_lemma(unsigned int x, struct sll *l)
/*@ requires take L = SLLseq(l);
    ensures take L_post = SLLseq(return);
            length(L_post) == 1u32 + length(L);
@*/
{
  struct sll *n = malloc_sll();
  n->data = x;
  n->next = l;
  return n;
}
