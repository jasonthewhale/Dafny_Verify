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