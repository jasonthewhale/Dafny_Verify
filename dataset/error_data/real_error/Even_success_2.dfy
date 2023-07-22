function has_even(v: bool, a: array<bool>, n: int): bool
reads a;
  requires n >= 0;
  requires n <= a.Length;
{
  if n == 0 then
    false
  else if a[n-1] == v then
    !has_even(v, a, n-1)
  else
    has_even(v, a, n-1)
}

method even_true(a: array<bool>, n: int) returns (even: bool)
  requires n >= 0;
  requires n <= a.Length;
  ensures has_even(true, a, n) <==> even;
{
  var i: int := 0;
  even := false;

  while(i < n)
    invariant 0 <= i <= n;
    invariant even <==> has_even(true, a, i);
  {
    if(a[i])
    {
      even := !even;
    }
    i := i + 1;
  }
}