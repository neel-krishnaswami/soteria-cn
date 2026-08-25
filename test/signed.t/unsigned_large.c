// Values at or above 2^31 in u32: correct only if specs compare unsigned.
unsigned int identity_big(unsigned int x)
/*@ requires 2147483648u32 <= x;
    ensures 1u32 <= return; return == x; @*/
{
  return x;
}

// Unsigned wrap-around: 0 - 1 is UINT_MAX.
unsigned int wraps(void)
/*@ ensures return == 4294967295u32; @*/
{
  unsigned int x = 0;
  return x - 1u;
}
