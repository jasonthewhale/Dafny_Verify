function has_count(v: int, a: array<int>, n: int): int
    reads a  // This allows the function to read from array 'a'
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
		invariant i <= n;
		invariant has_count (v, a, i) == r;
	{
		if (a[i] == v)
		{
			r := r + 1;
		}
		i := i + 1;
	}
}