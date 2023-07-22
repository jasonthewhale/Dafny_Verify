method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant forall k :: 0 <= k < n ==> forall i :: n <= i < a.Length ==> a[k] <= a[i]
    invariant forall k :: n <= k < a.Length ==> a[k] >= a[n]
  {
    var mindex, m := n, n + 1;
    while m < a.Length
      invariant n <= m <= a.Length
      invariant forall k :: n <= k < m ==> a[mindex] <= a[k]
      invariant forall k :: m <= k < a.Length ==> a[k] >= a[mindex]
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    var temp := a[mindex];
    a[mindex] := a[n];
    a[n] := temp;
    n := n + 1;
  }  
}