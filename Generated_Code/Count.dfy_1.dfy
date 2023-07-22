method count (v: int, a: array<int>, n: int) returns (r: int)
	requires n >= 0 && n <= a.Length;
	ensures has_count (v, a, n) == r;
{
	var i: int;

	i := 0;
	r := 0;

	while (i < n)
		invariant 0 <= i <= n
		invariant r == has_count(v, a, i)
	{
		if (a[i] == v)
		{
			r := r + 1;
		}
		i := i + 1;
	}
}