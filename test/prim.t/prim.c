// Bitwise operations, spec and body sides.
unsigned int bits(unsigned int x, unsigned int y)
/*@ ensures return == ((x & y) ^ (x | y)); @*/
{
  return (x & y) ^ (x | y);
}

// Shifts as multiplication.
unsigned int shift3(unsigned int x)
/*@ requires x < 1024u32;
    ensures return == x * 8u32; @*/
{
  return x << 3;
}

// Signed division.
int half(int a)
/*@ requires 0i32 <= a;
    ensures return == a / 2i32; @*/
{
  return a / 2;
}

// Struct values (PEstruct / PEmemberof or member stores).
struct point { int x; int y; };

int first_coord(int a)
/*@ ensures return == a; @*/
{
  struct point p = { a, 1 };
  return p.x;
}

// sizeof as a value.
unsigned long int_size(void)
/*@ ensures return == 4u64; @*/
{
  return sizeof(int);
}

// Spec builtins on pointers.
void prov(int *p)
/*@ requires take V = RW<int>(p);
             prov_eq(p, p);
             has_alloc_id(p);
    ensures  take V2 = RW<int>(p);
             V2 == V; @*/
{
}
