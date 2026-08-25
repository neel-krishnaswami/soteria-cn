unsigned int no_extract(unsigned int *p, unsigned long n, unsigned long k)
/*@ requires take A = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
             k < n;
    ensures take A_post = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
            return == A[k];
@*/
{
  return p[k];
}

void wrong_value(unsigned int *p, unsigned long n, unsigned long k, unsigned int v)
/*@ requires take A = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
             k < n;
    ensures take A_post = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
            A_post[k] == v + 1u32;
@*/
{
  /*@ extract RW<unsigned int>, k; @*/
  p[k] = v;
}
