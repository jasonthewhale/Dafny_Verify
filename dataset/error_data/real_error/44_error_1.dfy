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
}

Error:
'invariant 0 <= i <= k+1 && j == i * n': Error: this loop invariant could not be proved on entry
'invariant 0 <= i <= k+1 && j == i * n': Related message: loop invariant violation

Dafny program verifier finished with 0 verified, 1 error