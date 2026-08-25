// each() over a user-defined predicate with a scalar output.
/*@
predicate (i32) Cell(pointer p) {
  take V = RW<int>(p);
  return V;
}
@*/

// Round-trip: consume the each back unchanged.
void keep(int *a, unsigned long n)
/*@ requires take A = each(u64 i; i < n) { Cell(array_shift<int>(a, i)) };
    ensures  take A2 = each(u64 i; i < n) { Cell(array_shift<int>(a, i)) };
             A2 == A; @*/
{
}

// Extract one cell, read through it, and give everything back.
int get(int *a, unsigned long n, unsigned long k)
/*@ requires take A = each(u64 i; i < n) { Cell(array_shift<int>(a, i)) };
             k < n;
    ensures  take A2 = each(u64 i; i < n) { Cell(array_shift<int>(a, i)) };
             return == A[k]; @*/
{
  /*@ focus Cell, k; @*/
  return a[k];
}
