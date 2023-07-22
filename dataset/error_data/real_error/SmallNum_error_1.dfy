method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
	requires n > 0;
    requires n <= a.Length;
	requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
	ensures r <= max * n;
{
	var i: int;	

	i := 0;
	r := 0;

	while (i < n)
		invariant 0 <= i <= n;
		invariant r == sum(a, i);
	{
		r := r + a[i];
		i := i + 1;
	}
}

function sum(a: array<int>, n: int) returns (s: int)
	requires n >= 0;
	requires n <= a.Length;
	ensures s == sum(a, 0, n);
{
	if (n == 0) {
		s := 0;
	} else {
		s := sum(a, n - 1) + a[n - 1];
	}
}

function sum(a: array<int>, start: int, end: int) returns (s: int)
	requires 0 <= start <= end <= a.Length;
	ensures s == sum(a, start, end, 0);
{
	s := sum(a, start, end, 0);
}

function sum(a: array<int>, start: int, end: int, acc: int) returns (s: int)
	requires 0 <= start <= end <= a.Length;
	ensures s == acc + sum(a, start, end);
{
	if (start == end) {
		s := acc;
	} else {
		s := sum(a, start + 1, end, acc + a[start]);
	}
}

Error:
'function sum(a: array<int>, n: int) returns (s: int)': Error: colon expected
'if (n == 0) {': Error: then expected
's := 0;': Error: rbrace expected

3 parse errors detected in /Users/youjunchen/Desktop/Dafny/Generated_Code/SmallNum.dfy_1.dfy