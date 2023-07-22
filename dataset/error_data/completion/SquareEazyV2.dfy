method square (n: int, x: int) returns (r: int)
	requires 0 <= n;
	requires x == n;
	ensures r == x*n;
{
	var i: int;

	i := 0;
	r := 0;

	while (i < n)
	  invariant i <= n;
	  invariant r == i * n;
	{
		r := r + n;
		i := i + 1;
	}
}