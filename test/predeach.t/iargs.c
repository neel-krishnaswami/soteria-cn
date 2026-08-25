// each() over a predicate with an extra input argument.
/*@
predicate (i32) BoundedCell(pointer p, i32 lo) {
  take V = RW<int>(p);
  assert (lo <= V);
  return V;
}
@*/

void keep(int *a, unsigned long n, int lo)
/*@ requires take A = each(u64 i; i < n) { BoundedCell(array_shift<int>(a, i), lo) };
    ensures  take A2 = each(u64 i; i < n) { BoundedCell(array_shift<int>(a, i), lo) };
             A2 == A; @*/
{
}

int get(int *a, unsigned long n, int lo, unsigned long k)
/*@ requires take A = each(u64 i; i < n) { BoundedCell(array_shift<int>(a, i), lo) };
             k < n;
    ensures  take A2 = each(u64 i; i < n) { BoundedCell(array_shift<int>(a, i), lo) };
             lo <= return; @*/
{
  /*@ focus BoundedCell, k; @*/
  return a[k];
}
