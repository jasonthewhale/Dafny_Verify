method main(m: int, n: int) returns (x: int, y: int)
requires m >= 0
requires n >= 0
requires m < n
ensures y == n
{
    x := 0;
    y := m;

    while (x < n)
        invariant 0 <= x <= n
        invariant m <= y <= n
    {
        x := x + 1;
        if (x > m) 
        {
            y := y + 1;
        }
        else 
        {}
    }
}

Error:
'{': Error: a postcondition could not be proved on this return path
'ensures y == n': Related location: this is the postcondition that could not be proved
'invariant m <= y <= n': Error: this invariant could not be proved to be maintained by the loop
'invariant m <= y <= n': Related message: loop invariant violation

Dafny program verifier finished with 0 verified, 2 errors