void array_roundtrip(unsigned int (*p)[4])
/*@ requires take A = RW<unsigned int[4]>(p);
    ensures take A2 = RW<unsigned int[4]>(p);
            A2 == A;
@*/
{
}

void array_to_each(unsigned int (*p)[4])
/*@ requires take A = RW<unsigned int[4]>(p);
    ensures take B = each(u64 i; i < 4u64) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
            B == A;
@*/
{
}

void each_to_array(unsigned int (*p)[4])
/*@ requires take A = each(u64 i; i < 4u64) { RW<unsigned int>(array_shift<unsigned int>(p, i)) };
    ensures take B = RW<unsigned int[4]>(p);
            B == A;
@*/
{
}
