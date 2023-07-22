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