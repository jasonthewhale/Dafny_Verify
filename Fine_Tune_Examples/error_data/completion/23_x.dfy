method main(n: int) returns (sum: int, i: int)
requires n >= 0
{
    sum := 0;
    i := 0;
    while(i < n)
        invariant sum >= 0
        invariant 0 <= i <= n
    {
        sum := sum + i;
        i := i + 1;
    }
}