method main(n: int, k: int) returns (i :int, j: int)
    requires n >= 0
    requires k == 1 || k >= 0
    ensures k + i + j >= 2 * n
{
    i := 0;
    j := 0;
    while(i < n)
        invariant 0 <= i <= n
        invariant 0 <= j <= i * (i + 1) / 2
        invariant k + i + j >= 2 * n
    {
        i := i + 1;
        j := j + i;
    }
    assert k + i + j >= 2 * n;
    return (i, j);
}

Error:
'return (i, j);': Error: number of return parameters does not match declaration (found 1, expected 2)

1 resolution/type errors detected in 41.dfy_3.dfy