  $ soteria-cn verify parr.c
  parr.c:11:63: warning: annotation on array_shift suggests p has type unsigned int* but it has type unsigned int[4]*.
      ensures take B = each(u64 i; i < 4u64) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
                                                                ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
  parr.c:18:64: warning: annotation on array_shift suggests p has type unsigned int* but it has type unsigned int[4]*.
  /*@ requires take A = each(u64 i; i < 4u64) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
                                                                 ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
  Verifying function array_roundtrip...
  Successfully verified array_roundtrip
  Verifying function array_to_each...
  Successfully verified array_to_each
  Verifying function each_to_array...
  Successfully verified each_to_array
  $ soteria-cn verify parr_bad.c
  parr_bad.c:3:22: warning: annotation on RW suggests p has type unsigned int[5]* but it has type unsigned int[4]*.
      ensures take B = RW<unsigned int[5]>(p);
                       ^~~~~~~~~~~~~~~~~~~ 
  Verifying function too_long...
  error: Missing resource (under-specified) in too_long
      --> parr_bad.c:3:18
    1 | /  void too_long(unsigned int (*p)[4])
    2 | |  /*@ requires take A = RW<unsigned int[4]>(p);
    3 | |      ensures take B = RW<unsigned int[5]>(p);
      | |                   ^ Missing resource (could be hidden under a predicate?)
    4 | |  @*/
    5 | |  {
    6 | |  }
      | \--' 1: Verifying function
    7 |    
