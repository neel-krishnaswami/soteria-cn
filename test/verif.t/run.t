  $ soteria-cn verify min3.c -v
  Verifying function min3...
  Successfully verified min3
  Verifying function min3_invalid_spec...
  error: `Lfail (((V|1| <=u V|2|) && (V|3| <=u V|1|))) in min3_invalid_spec
      --> min3.c:21:13
   19 |      
   20 | /    unsigned int min3_invalid_spec(unsigned int x, unsigned int y, unsigned int z)
   21 | |    /*@ ensures return <= x
      | | /--------------^
   22 | | |              && return <= y
   23 | | |              && z <= return; // This doesn't hold
      | | \---------------------------^ Could not prove this holds
   24 | |    @*/
      . |    
   34 | |        }
   35 | |    }
      | \----' 1: Verifying function
   36 |      
  Verifying function min3_invalid_code...
  error: Null pointer dereference in min3_invalid_code
      --> min3.c:47:16
   36 |    
   37 | /  unsigned int min3_invalid_code(unsigned int x, unsigned int y, unsigned int z)
   38 | |  /*@ ensures return <= x
      . |  
   47 | |          return *((unsigned int*) 0);
      | |                 ^^^^^^^^^^^^^^^^^^^^ Invalid memory load
      . |  
   51 | |      }
   52 | |  }
      | \--' 1: Verifying function
   53 |    

  $ soteria-cn verify leak.c -v
  Verifying function to_verify...
  warning: Memory leak in to_verify
      --> leak.c:5:1
    4 |      
    5 |      int to_verify() {
      | /----'
      | | /--^
    6 | | |    int *p = malloc(sizeof(int));
      | | |             ------------------- 2: Memory allocated here leaked
    7 | | |    return 0;
    8 | | |  
      | \-|  ' 1: Verifying function
      |   \--^ Memory leftover after this function

  $ soteria-cn verify read.c
  Verifying function read...
  Successfully verified read
  Verifying function read_leak...
  warning: Memory leak in read_leak
      --> read.c:13:1
   12 |      
   13 |      unsigned int read_leak(unsigned int *p)
      | /----'
      | | /--^
   14 | | |  /*@
   15 | | |    requires take P = RW<unsigned int>(p);
      | | |                  - 2: Memory allocated here leaked
      . | |  
   18 | | |    return *p;
   19 | | |  }
      | \-|  ' 1: Verifying function
      |   \--^ Memory leftover after this function
   20 |      
  Verifying function read_invalid...
  error: Null pointer dereference in read_invalid
      --> read.c:24:10
   20 |    
   21 | /  unsigned int read_invalid(unsigned int *p)
   22 | |  /* no spec */
   23 | |  {
   24 | |    return *p;
      | |           ^^ Invalid memory load
   25 | |  }
      | \--' 1: Verifying function
   26 |    

  $ soteria-cn verify basic_incr.c
  Verifying function incr_unsigned...
  Successfully verified incr_unsigned
  Verifying function incr_signed_no_ovf...
  Successfully verified incr_signed_no_ovf
  Verifying function incr_signed_ovf...
  error: Integer overflow in incr_signed_ovf
      --> basic_incr.c:32:11
   24 |    
   25 | /  void incr_signed_ovf (int *p)
   26 | |  /*@ requires take P = RW<int>(p);
      . |  
   32 | |    int m = n + 1;
      | |            ^^^^^ Triggering operation
   33 | |    *p = m;
   34 | |  
      | \--' 1: Verifying function

  $ soteria-cn verify five_six.c
  Verifying function five_six...
  Successfully verified five_six
  Verifying function five_six_wrong...
  error: `Lfail (false) in five_six_wrong
      --> five_six.c:21:14
   15 |    
   16 | /  unsigned int five_six_wrong(unsigned int *p, unsigned int *q) 
   17 | |  /*@ requires take P = RW<unsigned int>(p);
      . |  
   21 | |               return == 6u32;
      | |               ^^^^^^^^^^^^^^ Could not prove this holds
      . |  
   26 | |      return *p;
   27 | |  
      | \--' 1: Verifying function

  $ soteria-cn verify transpose.c
  Verifying function transpose...
  Successfully verified transpose
  Verifying function transpose_wrong...
  error: `Lfail ((V|3| == V|4|)) in transpose_wrong
      --> transpose.c:21:13
   17 |    
   18 | /  void transpose_wrong (struct point *p) 
   19 | |  /*@ requires take P = RW<struct point>(p);
   20 | |      ensures take P_post = RW<struct point>(p);
   21 | |              P_post.x == P.x;
      | |              ^^^^^^^^^^^^^^^ Could not prove this holds
      . |  
   28 | |    p->y = temp_x;
   29 | |  }
      | \--' 1: Verifying function
   30 |    
  Verifying function transpose_wrong2...
  error: `Lfail ((V|3| == V|4|)) in transpose_wrong2
      --> transpose.c:34:13
   30 |    
   31 | /  void transpose_wrong2 (struct point *p) 
   32 | |  /*@ requires take P = RW<struct point>(p);
   33 | |      ensures take P_post = RW<struct point>(p);
   34 | |              P_post.x == P.x;
      | |              ^^^^^^^^^^^^^^^ Could not prove this holds
      . |  
   40 | |    p->x = temp_y;
   41 | |  
      | \--' 1: Verifying function

  $ soteria-cn verify init_point.c
  Verifying function zero...
  Successfully verified zero
  Verifying function init_point...
  Successfully verified init_point

  $ soteria-cn verify transpose2.c
  Verifying function swap...
  Successfully verified swap
  Verifying function transpose2...
  Successfully verified transpose2

  $ soteria-cn verify get_and_free.c
  Verifying function malloc_and_set...
  Successfully verified malloc_and_set
  Verifying function get_and_free...
  Successfully verified get_and_free
  Verifying function tester...
  Successfully verified tester

  $ soteria-cn verify incr2_alias.c
  Verifying function incr2a...
  Successfully verified incr2a
  Verifying function incr2b...
  Successfully verified incr2b
  Verifying function call_both...
  Successfully verified call_both

  $ soteria-cn verify simpl_pred.c
  Verifying function incr2...
  Successfully verified incr2
  Verifying function call_both_better...
  Successfully verified call_both_better

  $ soteria-cn verify lists.c
  Verifying function empty_list...
  Successfully verified empty_list
  Verifying function prepend...
  Successfully verified prepend
  Verifying function free_list...
  Successfully verified free_list
  Verifying function slcopy...
  Successfully verified slcopy
  Verifying function slappend...
  Successfully verified slappend
  Verifying function length...
  Successfully verified length
  Verifying function test1...
  Successfully verified test1
  Verifying function test2...
  Successfully verified test2
  Verifying function test3...
  Successfully verified test3
  Verifying function test4...
  Successfully verified test4
  Verifying function test5...
  Successfully verified test5
  Verifying function test6...
  Successfully verified test6

  $ soteria-cn verify dll.c
  Verifying function empty_list...
  Successfully verified empty_list
  Verifying function prepend...
  Successfully verified prepend
  Verifying function free_at...
  Successfully verified free_at
  Verifying function free_dll...
  Successfully verified free_dll
  Verifying function copy_at...
  Successfully verified copy_at
  Verifying function dllcopy...
  Successfully verified dllcopy
  Verifying function length_at...
  Successfully verified length_at
  Verifying function length...
  Successfully verified length
  Verifying function test1...
  Successfully verified test1
  Verifying function test2...
  Successfully verified test2
  Verifying function test3...
  Successfully verified test3
  Verifying function test4...
  Successfully verified test4
