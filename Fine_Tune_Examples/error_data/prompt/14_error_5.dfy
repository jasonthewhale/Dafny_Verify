method main(m: int) returns (a: int)
    requires m > 0
    ensures a >= -m
    ensures a <= m
{
    a := 0;
    var j: int := 1;

    while (j <= m)
        invariant 1 <= j <= m + 1
        invariant -m - 1 <= a <= m + 1
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
'-m - 1 <= a' in 'invariant -m - 1 <= a <= m + 1': Error: this invariant could not be proved to be maintained by the loop
'-m - 1 <= a' in 'invariant -m - 1 <= a <= m + 1': Related message: loop invariant violation
'a <= m + 1' in 'invariant -m - 1 <= a <= m + 1': Error: this invariant could not be proved to be maintained by the loop
'a <= m + 1' in 'invariant -m - 1 <= a <= m + 1': Related message: loop invariant violation
'return' in 'return a;': Error: a postcondition could not be proved on this return path
'a >= -m' in 'ensures a >= -m': Related location: this is the postcondition that could not be proved
'return' in 'return a;': Error: a postcondition could not be proved on this return path
'a <= m' in 'ensures a <= m': Related location: this is the postcondition that could not be proved
Dafny program verifier finished with 0 verified, 4 errors