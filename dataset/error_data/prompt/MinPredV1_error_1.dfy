method min(a: array<int>, n: int) returns (min: int)
  requires n > 0 && n <= a.Length;
  ensures contains(min, a, n);
  ensures lower_bound(min, a, n);
{
  var i: int;
  min := a[0];
  i := 1;

  while i < n
    invariant 0 <= i <= n;
    invariant forall j: int :: 0 <= j < i ==> a[j] >= min;
  {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
}

Error:
'ensures contains(min, a, n);': Error: unresolved identifier: contains
'ensures lower_bound(min, a, n);': Error: unresolved identifier: lower_bound

2 resolution/type errors detected in MinPredV1.dfy_1.dfy
Hint: remember to include original helper functions or methods (do not change anything) if provided.