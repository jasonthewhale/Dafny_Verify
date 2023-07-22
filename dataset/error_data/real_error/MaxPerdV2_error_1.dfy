method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
{
  var i: int := 1;

  max := a[0];

  while i < n
    invariant 1 <= i <= n &&
              max == a[0..i-1].Max() &&
              upper_bound(max, a, i) &&
              contains(max, a, i);
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}

Error:
'ensures is_max(max, a, n);': Error: unresolved identifier: is_max
'max == a[0..i-1].Max() &&': Error: type seq<?> does not have a member Max
'upper_bound(max, a, i) &&': Error: unresolved identifier: upper_bound
'contains(max, a, i);': Error: unresolved identifier: contains

4 resolution/type errors detected in MaxPerdV2.dfy_1.dfy
Hint: remember to include original helper functions or methods (do not change anything) if provided.