  $ soteria-cn verify seq.c
  Verifying function constructors_work...
  Successfully verified constructors_work
  Verifying function hd_or_zero...
  Successfully verified hd_or_zero
  $ soteria-cn verify seq.c --dump-smt smt.log -f hd_or_zero > /dev/null 2>&1
  $ grep -c "declare-datatypes" smt.log > /dev/null && echo "datatypes declared"
  datatypes declared
  $ soteria-cn verify seq_bad.c
  Verifying function constructors_work...
  error: `Lfail (false) in constructors_work
      --> seq_bad.c:15:13
   12 |    
   13 | /  void constructors_work(void)
   14 | |  /*@ requires let s = Seq_Cons { head: 42u32, tail: Seq_Nil {} };
   15 | |      ensures (match s { Seq_Nil {} => { 21u32 } Seq_Cons { head: h, tail: _ } => { h } }) == 41u32;
      | |              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Could not prove this holds
   16 | |  @*/
   17 | |  {
   18 | |  }
      | \--' 1: Verifying function
   19 |    
