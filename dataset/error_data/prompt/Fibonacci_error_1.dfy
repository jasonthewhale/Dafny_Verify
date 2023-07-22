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
'ensures x == Fib(n)': Error: unresolved identifier: Fib
'invariant x == Fib(i) && y == Fib(i + 1)': Error: unresolved identifier: Fib
'invariant x == Fib(i) && y == Fib(i + 1)': Error: unresolved identifier: Fib

3 resolution/type errors detected in Fibonacci.dfy_1.dfy
Hint: remember to include original helper functions or methods (do not change anything) if provided.