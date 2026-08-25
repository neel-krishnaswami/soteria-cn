Signedness: Core mathematical integers are embedded order-preservingly at
[math_bits] (conv_int extends by the source type's signedness), wrapI wraps
and catch_exceptional_condition range-checks against the target C type, and
spec comparisons take their signedness from the operands' base type.

Cross-checked against `cn verify` (all verdicts agree): identity_big, wraps
and count_up pass; inc fails (signed overflow).

  $ soteria-cn verify unsigned_large.c
  Verifying function identity_big...
  Successfully verified identity_big
  Verifying function wraps...
  Successfully verified wraps
  $ soteria-cn verify count_u.c
  Verifying function count_up...
  Successfully verified count_up
  $ soteria-cn verify overflow_bad.c
  Verifying function inc...
  error: Integer overflow in inc
      --> overflow_bad.c:5:10
    1 |    // Signed overflow is UB: x + 1 is not provably in range for int.
    2 | /  int inc(int x)
    3 | |  /*@ ensures true; @*/
    4 | |  {
    5 | |    return x + 1;
      | |           ^^^^^ Triggering operation
    6 | |  }
      | \--' 1: Verifying function
    7 |    
