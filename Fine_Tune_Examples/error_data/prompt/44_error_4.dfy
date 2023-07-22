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
        assert i <= k+1; // additional assertion to help the verifier
    }
    assert i == j; // additional assertion to help the verifier
}

Error:
'i <= k+1' in 'invariant 0 <= i <= k+1 && j == i * n': Error: this loop invariant could not be proved on entry
'i <= k+1' in 'invariant 0 <= i <= k+1 && j == i * n': Related message: loop invariant violation
'i == j' in 'assert i == j; // additional assertion to help the verifier': Error: assertion might not hold
Dafny program verifier finished with 0 verified, 2 errors