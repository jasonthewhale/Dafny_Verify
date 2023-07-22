ghost function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
{
    p := 1;
    var i := 0;
    while i != n
        invariant 0 <= i <= n
        invariant p == Power(i)
    {
        i := i + 1;
        p := p * 2;
    }
}

method ComputePower2(n: nat) returns (p: nat)

{
    p := 1;
    var i := 0;
    while i != n
        invariant 0 <= i <= n
        invariant p * Power(n - i) == Power(n)
}