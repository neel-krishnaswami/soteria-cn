  $ soteria-cn verify arr.c
  arr.c:9:7: warning: deprecated keyword 'extract', use 'focus' instead
    /*@ extract RW<unsigned int>, k; @*/
        ^~~~~~~ 
  Verifying function read_cell...
  Successfully verified read_cell
  Verifying function write_cell...
  Successfully verified write_cell
  Verifying function read_bounded...
  Successfully verified read_bounded
  $ soteria-cn verify arr_bad.c
  arr_bad.c:18:7: warning: deprecated keyword 'extract', use 'focus' instead
    /*@ extract RW<unsigned int>, k; @*/
        ^~~~~~~ 
  Verifying function no_extract...
  error: Null pointer dereference in no_extract
      --> arr_bad.c:8:10
    1 | /  unsigned int no_extract(unsigned int *p, unsigned long n, unsigned long k)
    2 | |  /*@ requires take A = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
      . |  
    8 | |    return p[k];
      | |           ^^^^ Invalid memory load
    9 | |  }
      | \--' 1: Verifying function
   10 |    
  Verifying function wrong_value...
  error: `Lfail (false) in wrong_value
      --> arr_bad.c:15:13
   10 |    
   11 | /  void wrong_value(unsigned int *p, unsigned long n, unsigned long k, unsigned int v)
   12 | |  /*@ requires take A = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
      . |  
   15 | |              A_post[k] == v + 1u32;
      | |              ^^^^^^^^^^^^^^^^^^^^^ Could not prove this holds
      . |  
   19 | |    p[k] = v;
   20 | |  }
      | \--' 1: Verifying function
   21 |    
