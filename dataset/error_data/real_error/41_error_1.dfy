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
}

Error:
'invariant k + i + j >= 2 * n': Error: this loop invariant could not be proved on entry
'invariant k + i + j >= 2 * n': Related message: loop invariant violation

Dafny program verifier finished with 0 verified, 1 error