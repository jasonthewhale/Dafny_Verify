method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
{
    p := 1;
    var i := 0;
    while i != n
        invariant 0 <= i <= n && p == Power(i)
    {
        i := i + 1;
        p := p * 2;
    }
}

Error:
'ensures p == Power(n)': Error: unresolved identifier: Power
'invariant 0 <= i <= n && p == Power(i)': Error: unresolved identifier: Power

2 resolution/type errors detected in ComputePower.dfy_1.dfy
Hint: remember to include original helper functions or methods (do not change anything) if provided.