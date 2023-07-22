method min(a: array<int>, n: int) returns (min: int)
  requires 0 < n <= a.Length;
  ensures is_min(min, a, n);
{
  var i: int;
  min := a[0];
  i := 1;

  while i < n
    invariant 1 <= i <= n;
    invariant forall j: int :: 0 <= j < i ==> a[j] >= min;
  {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
}

Error:
'ensures is_min(min, a, n);': Error: unresolved identifier: is_min

1 resolution/type errors detected in MinPredV2.dfy_1.dfy
Hint: remember to include original helper functions or methods (do not change anything) if provided.