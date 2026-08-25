// each() with an explicit concrete range compiles to EachI, which both tools
// expand into a finite conjunction. (The guard form `each(u64 i; i < 4u64)`
// in constraint position compiles to Forall instead, which neither tool can
// use without instantiate.)
void keep_zeros(unsigned int *a)
/*@ requires take A = each(u64 i; i < 4u64) { RW<unsigned int>(array_shift<unsigned int>(a, i)) };
             each(u64 i : 0, 3; A[i] == 0u32);
    ensures  take A2 = each(u64 i; i < 4u64) { RW<unsigned int>(array_shift<unsigned int>(a, i)) };
             A2[2u64] == 0u32; @*/
{
}

// Negative: the conjunction does not make A[2] equal to 1.
void keep_zeros_bad(unsigned int *a)
/*@ requires take A = each(u64 i; i < 4u64) { RW<unsigned int>(array_shift<unsigned int>(a, i)) };
             each(u64 i : 0, 3; A[i] == 0u32);
    ensures  take A2 = each(u64 i; i < 4u64) { RW<unsigned int>(array_shift<unsigned int>(a, i)) };
             A2[2u64] == 1u32; @*/
{
}
