c

method even_true(a: array<bool>, n: int) returns (even: bool)
  requires n >= 0;
  requires n <= a.Length;
  ensures has_even(true, a, n) <==> even;
{
  var i: int := 0;
  even := false;

  while(i < n)
    invariant i <= n;
    invariant has_even(true, a, i) <==> even;
  {
    if(a[i])
    {
      even := !even;
    }
    i := i + 1;
  }
}
