method main(n: int) returns (c: int, i: int)
requires n > 0
ensures c >= 0
{
    c := 0;
    i := 0;
    while(i < n)
    {
        c := c + i;
        i := i + 1;
    }
}