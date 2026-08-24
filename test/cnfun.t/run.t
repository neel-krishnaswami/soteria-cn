  $ soteria-cn verify funs.c
  Verifying function add3...
  Successfully verified add3
  Verifying function scale...
  Successfully verified scale
  Verifying function length_one...
  Successfully verified length_one
  Verifying function push...
  Successfully verified push
  $ soteria-cn verify funs.c --dump-smt smt.log -f push > /dev/null 2>&1
  $ grep -c "declare-fun length" smt.log > /dev/null && echo "length declared"
  length declared
  $ soteria-cn verify funs_bad.c
  Verifying function length_wrong...
  error: `Lfail ((length(Seq_Cons(Seq_Nil(), 0x00000007)) == 0x00000002)) in length_wrong
      --> funs_bad.c:17:13
   14 |    
   15 | /  void length_wrong(void)
   16 | |  /*@ requires let s = Seq_Cons { head: 7u32, tail: Seq_Nil {} };
   17 | |      ensures length(s) == 2u32;
      | |              ^^^^^^^^^^^^^^^^^ Could not prove this holds
      . |  
   21 | |    /*@ unfold length(Seq_Nil {}); @*/
   22 | |  }
      | \--' 1: Verifying function
   23 |    
