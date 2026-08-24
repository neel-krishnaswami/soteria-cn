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

function (u32) plus3 (u32 x) {
  x + 3u32
}

function (u32) scale_or_cap (u32 x) {
  if (x < 100u32) { 3u32 * x } else { 300u32 }
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

unsigned int add3(unsigned int x)
/*@ ensures return == plus3(x); @*/
{
  return x + 3;
}

unsigned int scale(unsigned int x)
/*@ requires x < 100u32;
    ensures return == scale_or_cap(x); @*/
{
  return 3 * x;
}

void length_one(void)
/*@ requires let s = Seq_Cons { head: 7u32, tail: Seq_Nil {} };
    ensures length(s) == 1u32;
@*/
{
  /*@ unfold length(Seq_Cons { head: 7u32, tail: Seq_Nil {} }); @*/
  /*@ unfold length(Seq_Nil {}); @*/
}

struct sll *push(unsigned int x, struct sll *l)
/*@ requires take L = SLLseq(l);
    ensures take L_post = SLLseq(return);
            L_post == Seq_Cons { head: x, tail: L };
            length(L_post) == 1u32 + length(L);
@*/
{
  struct sll *n = malloc_sll();
  n->data = x;
  n->next = l;
  /*@ unfold length(Seq_Cons { head: x, tail: L }); @*/
  return n;
}
