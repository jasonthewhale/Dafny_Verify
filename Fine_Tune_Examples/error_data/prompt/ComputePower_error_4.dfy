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
    {
        i := i + 1;
        p := p * 2;
    }
}

Error:
'while' in 'while i != n': Error: a postcondition could not be proved on this return path
'p == Power(n)' in 'ensures p == Power(n)': Related location: this is the postcondition that could not be proved
Dafny program verifier finished with 1 verified, 1 error