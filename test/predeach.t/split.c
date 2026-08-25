// Rejoin an each() from two half-range chunks (multi-chunk assembly).
void join_halves(int *a, unsigned long n, unsigned long m)
/*@ requires m <= n;
             take A = each(u64 i; i < m) { RW<int>(array_shift<int>(a, i)) };
             take B = each(u64 i; m <= i && i < n) { RW<int>(array_shift<int>(a, i)) };
    ensures  take C = each(u64 i; i < n) { RW<int>(array_shift<int>(a, i)) }; @*/
{
}

// Fails in both CN and soteria-cn: the merged map's per-index equalities are
// quantified facts created during the ensures consume, too late for any
// body-side instantiate to expose them.
int join_get(int *a, unsigned long n, unsigned long m, unsigned long k)
/*@ requires m <= n; k < m;
             take A = each(u64 i; i < m) { RW<int>(array_shift<int>(a, i)) };
             take B = each(u64 i; m <= i && i < n) { RW<int>(array_shift<int>(a, i)) };
    ensures  take C = each(u64 i; i < n) { RW<int>(array_shift<int>(a, i)) };
             C[k] == A[k]; @*/
{
  return 0;
}
