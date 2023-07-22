method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant forall k :: 0 <= k < n ==> forall i :: n <= i < a.Length ==> a[k] <= a[i]
  {
    var mindex, m := n, n;
    while m < a.Length
      invariant n <= m <= a.Length
      invariant forall k :: n <= k < m ==> a[mindex] <= a[k]
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    a[mindex], a[n] := a[n], a[mindex];
    n := n + 1;
  }  
}