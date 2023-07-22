method main(m: int) returns (a: int)
    requires m > 0
    ensures a >= -m
    ensures a <= m
{
    a := 0;
    var j: int := 1;

    while (j <= m)
        invariant 1 <= j <= m + 1
        invariant -m <= a <= m
    {
        if (*)
        {
            a := a + 1;
        }
        else
        {
            a := a - 1;
        }

        j := j + 1;
    }

    return a;
}

Error:
'-m <= a' in 'invariant -m <= a <= m': Error: this invariant could not be proved to be maintained by the loop
'-m <= a' in 'invariant -m <= a <= m': Related message: loop invariant violation
'a <= m' in 'invariant -m <= a <= m': Error: this invariant could not be proved to be maintained by the loop
'a <= m' in 'invariant -m <= a <= m': Related message: loop invariant violation
Dafny program verifier finished with 0 verified, 2 errors