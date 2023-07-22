method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
{
    p := 1;
    var i := 0;
    while i != n
        invariant 0 <= i <= n && p == 2^i
    {
        i := i + 1;
        p := p * 2;
    }
}