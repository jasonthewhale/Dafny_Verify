function contains(v: int, a: array<int>, n: int): bool 
reads a
  requires n >= 0 && n <= a.Length
{
  exists j: int :: 0 <= j < n && a[j] == v
}

function lower_bound(v: int, a: array<int>, n: int): bool 
reads a
  requires n >= 0 && n <= a.Length
{
  forall j: int :: 0 <= j < n ==> a[j] >= v
}

function is_min(m: int, a: array<int>, n: int): bool 
reads a
  requires n >= 0 && n <= a.Length
{
  contains(m, a, n) && lower_bound(m, a, n)
}

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
    invariant is_min(min, a, i);
  {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
}