method main(n: int, k: int) returns (i: int, j :int)
requires n ==1 || n == 2
ensures (n != 1) || (i == j)
{
    i := 0;
    j := 0;
    while(i <= k)
        invariant 0 <= i <= k+1 && j == i * n
    {
        i := i + 1;
        j := j + n;
    }
    assert i == j; // additional assertion to help the verifier
}