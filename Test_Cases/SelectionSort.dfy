method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant forall i,j :: 0 <=i < n <= j <a.Length ==> a[i] <= a[j] 
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var mindex, m := n, n;
    while m != a.Length
      invariant 0 <= n <= m <= a.Length
      invariant n <= mindex < a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
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

method SelectionSort1(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant forall i :: n <= i < a.Length ==> multiset(a[n..]) == old(multiset(a[n..]))
  {
    var mindex, m := n, n;
    while m != a.Length
      invariant n <= m <= a.Length
      invariant mindex == n || (n <= mindex < m && a[mindex] <= a[m])
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
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

