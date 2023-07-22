method max(a: array<int>, n: int) returns (max: int)
  requires n > 0;
  requires n <= a.Length;
  ensures exists i :: 0 <= i < n && a[i] == max;
  ensures forall i :: 0 <= i < n ==> a[i] <= max;
{
  var i: int;

  max := a[0];
  i := 1;

  while i < n
    invariant 0 <= i <= n;
    invariant forall j :: 0 <= j < i ==> a[j] <= max;
    invariant exists k :: 0 <= k < i && a[k] == max;
  {
    if (a[i] > max) {
      max := a[i];
    }
    i := i + 1;
  }
}