method main(n: int) returns (x: int)
requires n > 0
ensures x == n
{
    x := 0;
    while(x < n)
    invariant 0 <= x <= n
    {
        x := x + 1;
    }
}