// Free a whole list with a loop whose invariant is the list predicate over
// the not-yet-freed suffix.
struct sllist {
  int head;
  struct sllist* tail;
};

typedef struct sllist* SLL;

/*@
predicate [rec] (u32) SLList_At(pointer p) {
  if (is_null(p)) {
    return 0u32;
  } else {
    take H = RW<struct sllist>(p);
    take L = SLList_At(H.tail);
    return (1u32 + L);
  }
}
@*/

extern struct sllist *free_sllist_node (struct sllist *node);
/*@ spec free_sllist_node(pointer node);
    requires take P = RW<struct sllist>(node);
    ensures true;
@*/

void free_all(SLL p)
/*@ requires take L = SLList_At(p); @*/
{
  while (p != 0)
  /*@ inv take L2 = SLList_At(p); @*/
  {
    SLL next = p->tail;
    free_sllist_node(p);
    p = next;
  }
}
