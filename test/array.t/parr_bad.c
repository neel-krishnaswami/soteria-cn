void too_long(unsigned int (*p)[4])
/*@ requires take A = RW<unsigned int[4]>(p);
    ensures take B = RW<unsigned int[5]>(p);
@*/
{
}
