function has_count(v: int, a: array<int>, n: int): int
    reads a
    requires n >= 0 && n <= a.Length
{
    if n == 0 then 0 else
    (if a[n-1] == v then has_count(v, a, n-1) + 1 else has_count(v, a, n-1))
}


method count (v: int, a: array<int>, n: int) returns (r: int)
	requires n >= 0 && n <= a.Length;
	ensures has_count (v, a, n) == r;
{
	var i: int;

	i := 0;
	r := 0;

	while (i < n)
		invariant has_count (v, a, i) == r;
	{
		if (a[i] == v)
		{
			r := r + 1;
		}
		i := i + 1;
	}
}

Error:
'while' in 'while (i < n)': Error: a postcondition could not be proved on this return path
'has_count (v, a, n) == r' in 'ensures has_count (v, a, n) == r;': Related location: this is the postcondition that could not be proved
'has_count (v, a, i)' in 'invariant has_count (v, a, i) == r;': Error: function precondition might not hold
'n <= a.Length' in 'requires n >= 0 && n <= a.Length': Related location
Dafny program verifier finished with 2 verified, 2 errors