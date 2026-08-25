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

lemma length_cons_pure (u32 x, datatype seq l)
  requires
      true;
  ensures
      length(Seq_Cons { head: x, tail: l }) == 1u32 + length(l);

lemma length_cons_fact (pointer p, u32 x)
  requires
      take L = SLLseq(p);
  ensures
      take L_post = SLLseq(p);
      L_post == L;
      length(Seq_Cons { head: x, tail: L }) == 1u32 + length(L);
@*/

extern struct sll *malloc_sll ();
/*@ spec malloc_sll();
    ensures take P = W<struct sll>(return);
@*/

struct sll *push_with_lemma(unsigned int x, struct sll *l)
/*@ requires take L = SLLseq(l);
    ensures take L_post = SLLseq(return);
            L_post == Seq_Cons { head: x, tail: L };
            length(L_post) == 1u32 + length(L);
@*/
{
  struct sll *n = malloc_sll();
  n->data = x;
  n->next = l;
  /*@ apply length_cons_fact(l, x); @*/
  return n;
}

struct sll *push_with_pure_lemma(unsigned int x, struct sll *l)
/*@ requires take L = SLLseq(l);
    ensures take L_post = SLLseq(return);
            length(L_post) == 1u32 + length(L);
@*/
{
  struct sll *n = malloc_sll();
  n->data = x;
  n->next = l;
  /*@ apply length_cons_pure(x, L); @*/
  return n;
}
