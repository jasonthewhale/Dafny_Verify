method square (n: int) returns (r: int)
	requires 0 <= n;
	ensures r == n*n;
{
	var i: int;

	i := 0;
	r := 0;

	while (i < n)
	{
		r := r + n;
		i := i + 1;
	}
}
