unsigned int read_cell(unsigned int *p, unsigned long n, unsigned long k)
/*@ requires take A = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
             k < n;
    ensures take A_post = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
            A_post == A;
            return == A[k];
@*/
{
  /*@ extract RW<unsigned int>, k; @*/
  return p[k];
}

void write_cell(unsigned int *p, unsigned long n, unsigned long k, unsigned int v)
/*@ requires take A = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
             k < n;
    ensures take A_post = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
            A_post[k] == v;
@*/
{
  /*@ extract RW<unsigned int>, k; @*/
  p[k] = v;
}

unsigned int read_bounded(unsigned int *p, unsigned long n, unsigned long k)
/*@ requires take A = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
             each (u64 i; i < n) { A[i] < 100u32 };
             k < n;
    ensures take A_post = each(u64 i; i < n) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
            A_post == A;
            return < 100u32;
@*/
{
  /*@ extract RW<unsigned int>, k; @*/
  /*@ instantiate k; @*/
  return p[k];
}
