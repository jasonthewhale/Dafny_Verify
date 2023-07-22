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
    invariant even ==> has_even(true, a, i);
  {
    if(a[i])
    {
      even := !even;
    }
    i := i + 1;
  }
}

Error:
'while' in 'while(i < n)': Error: a postcondition could not be proved on this return path
'has_even(true, a, n) <==> even' in 'ensures has_even(true, a, n) <==> even;': Related location: this is the postcondition that could not be proved
'has_even(true, a, i)' in 'invariant even ==> has_even(true, a, i);': Error: this invariant could not be proved to be maintained by the loop
'has_even(v, a, n-1)' in '!has_even(v, a, n-1)': Related location
'has_even(true, a, i)' in 'invariant even ==> has_even(true, a, i);': Related message: loop invariant violation
'has_even(v, a, n-1)' in '!has_even(v, a, n-1)': Related location
Dafny program verifier finished with 2 verified, 2 errors