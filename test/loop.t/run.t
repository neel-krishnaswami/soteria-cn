Loop invariants (CN discipline): a loop label's argument type is its
invariant; jumping to the label consumes it and requires an empty footprint,
and the label body is verified as a separate obligation.

Cross-checked against `cn verify` (all verdicts agree): count_up, zero and
free_all pass; count_bad (invariant not preserved), count_weak (invariant too
weak for the post) and needs_inv (auto-invariant too weak) fail.

  $ soteria-cn verify count.c
  Verifying function count_up...
  Successfully verified count_up
  $ soteria-cn verify count_bad.c
  Verifying function count_bad...
  error: `Lfail ((V|8| == 0xffffffff)) in count_bad
      --> count_bad.c:9:22
    7 |      int i = 0;
    8 | /    while (i < n)
    9 | |    /*@ inv 0i32 <= i; i == 0i32; n < 1000i32; {n} unchanged; @*/
      | |                       ^^^^^^^^^ Could not prove this holds
   10 | |    {
   11 | |      i = i + 1;
   12 | |    }
      | \----' 1: Verifying function
   13 |      return i;
  $ soteria-cn verify count_weak.c
  Verifying function count_weak...
  error: `Lfail ((V|1| == V|8|)) in count_weak
      --> count_weak.c:5:13
    5 |        ensures return == n; @*/
      |                ^^^^^^^^^^^ Could not prove this holds
    6 |    {
    7 |      int i = 0;
    8 | /    while (i < n)
    9 | |    /*@ inv 0i32 <= i; n < 1000i32; {n} unchanged; @*/
   10 | |    {
   11 | |      i = i + 1;
   12 | |    }
      | \----' 1: Verifying function
   13 |      return i;
  $ soteria-cn verify no_inv.c
  Verifying function zero...
  Successfully verified zero
  Verifying function needs_inv...
  error: `Lfail ((0x00000000 == V|5|)) in needs_inv
      --> no_inv.c:14:13
   14 |  /*@ ensures return == 0i32; @*/
      |              ^^^^^^^^^^^^^^ Could not prove this holds
      .  
   17 |    while (i > 0) { i = i - 1; }
      |    ---------------------------- 1: Verifying function
  $ soteria-cn verify list_free.c
  Verifying function free_all...
  Successfully verified free_all
