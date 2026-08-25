// each() over a predicate with a record output: the map's value sort is a
// record, encoded as a single-constructor SMT datatype.
struct pair { int x; int y; };

/*@
predicate {i32 x, i32 y} PairAt(pointer p) {
  take P = RW<struct pair>(p);
  return {x: P.x, y: P.y};
}
@*/

void keep_pairs(struct pair *a, unsigned long n)
/*@ requires take M = each(u64 i; i < n) { PairAt(array_shift<struct pair>(a, i)) };
    ensures  take M2 = each(u64 i; i < n) { PairAt(array_shift<struct pair>(a, i)) };
             M2 == M; @*/
{
}

int get_x(struct pair *a, unsigned long n, unsigned long k)
/*@ requires take M = each(u64 i; i < n) { PairAt(array_shift<struct pair>(a, i)) };
             k < n;
    ensures  take M2 = each(u64 i; i < n) { PairAt(array_shift<struct pair>(a, i)) };
             return == M[k].x; @*/
{
  /*@ focus PairAt, k; @*/
  return a[k].x;
}
