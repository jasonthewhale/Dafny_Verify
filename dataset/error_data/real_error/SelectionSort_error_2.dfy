method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall k :: 0 <= k < n ==> forall j :: n <= j < a.Length ==> a[k] <= a[j]
  {
    var mindex, m := n, n;
    while m != a.Length
      invariant n <= m <= a.Length
      invariant forall k :: n <= k < m ==> a[mindex] <= a[k]
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    if mindex != n {
      var temp := a[mindex];
      a[mindex] := a[n];
      a[n] := temp;
    }
    n := n + 1;
  }  
}

Error:
'while n != a.Length': Error: a postcondition could not be proved on this return path
'ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]': Related location: this is the postcondition that could not be proved
'==>': Related location
'<=': Related location
'invariant forall k :: 0 <= k < n ==> forall j :: n <= j < a.Length ==> a[k] <= a[j]': Error: this invariant could not be proved to be maintained by the loop
'invariant forall k :: 0 <= k < n ==> forall j :: n <= j < a.Length ==> a[k] <= a[j]': Related message: loop invariant violation
'a[mindex]': Error: index out of range
'a[mindex]': Error: index out of range
'a[mindex];': Error: index out of range

Dafny program verifier finished with 1 verified, 5 errors