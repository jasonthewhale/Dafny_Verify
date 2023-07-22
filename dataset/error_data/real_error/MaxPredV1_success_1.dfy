method max(a: array<int>, n: int) returns (max: int)
  requires n > 0;
  requires n <= a.Length;
  ensures exists j :: 0 <= j < n && a[j] == max;
  ensures forall j :: 0 <= j < n ==> a[j] <= max;
{
  var i: int;
  max := a[0];
  i := 1;

  while i < n
    invariant 0 <= i <= n;
    invariant exists j :: 0 <= j < i && a[j] == max;
    invariant forall j :: 0 <= j < i ==> a[j] <= max;
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}