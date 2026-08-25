each() completion: user-defined predicate cells (scalar and record outputs),
extra input arguments (iargs), multi-chunk assembly, and EachI expansion.

Cross-checked against `cn verify` (all verdicts agree):
- cells.c: keep and get pass (scalar-output predicate each, focus + auto
- pairs.c: keep_pairs and get_x pass (record-output predicate each; record
- iargs.c: keep and get pass (predicate each with an extra input argument).
- split.c: join_halves passes (an each() consumed from two half-range
- eachi.c: keep_zeros passes, keep_zeros_bad fails (explicit-range each

  $ soteria-cn verify cells.c
  Verifying function keep...
  Successfully verified keep
  Verifying function get...
  Successfully verified get
  $ soteria-cn verify pairs.c
  Verifying function keep_pairs...
  Successfully verified keep_pairs
  Verifying function get_x...
  Successfully verified get_x
  $ soteria-cn verify iargs.c
  Verifying function keep...
  Successfully verified keep
  Verifying function get...
  Successfully verified get
  $ soteria-cn verify split.c
  Verifying function join_halves...
  Successfully verified join_halves
  Verifying function join_get...
  error: `Lfail ((V|25|[V|5|] == V|6|[V|5|])) in join_get
      --> split.c:18:14
   12 |    // body-side instantiate to expose them.
   13 | /  int join_get(int *a, unsigned long n, unsigned long m, unsigned long k)
   14 | |  /*@ requires m <= n; k < m;
      . |  
   18 | |               C[k] == A[k]; @*/
      | |               ^^^^^^^^^^^^ Could not prove this holds
   19 | |  {
   20 | |    return 0;
   21 | |  }
      | \--' 1: Verifying function
   22 |    
  $ soteria-cn verify eachi.c
  Verifying function keep_zeros...
  Successfully verified keep_zeros
  Verifying function keep_zeros_bad...
  error: `Lfail ((0x00000001 == V|3|[0x0000000000000002])) in keep_zeros_bad
      --> eachi.c:18:14
   13 |    // Negative: the conjunction does not make A[2] equal to 1.
   14 | /  void keep_zeros_bad(unsigned int *a)
   15 | |  /*@ requires take A = each(u64 i; i < 4u64) { RW<unsigned int>(array_shift<unsigned int>(a, i)) };
      . |  
   18 | |               A2[2u64] == 1u32; @*/
      | |               ^^^^^^^^^^^^^^^^ Could not prove this holds
   19 | |  {
   20 | |  }
      | \--' 1: Verifying function
   21 |    
