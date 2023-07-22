function Fib(n: nat): nat {
 if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}

method ComputeFib(n: nat) returns (x: nat)
    ensures x == Fib(n)
{
    x := 0;
    var i := 0;
    var y := 1;
    while i != n
        invariant x == Fib(i) && y == Fib(i + 1)
    {
        x, y := y, x + y;
        i := i + 1;
    }
}

Error:
'while i != n': Error: cannot prove termination; try supplying a decreases clause for the loop

Dafny program verifier finished with 1 verified, 1 error