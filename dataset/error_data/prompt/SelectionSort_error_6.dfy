method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i,j :: 0 <= i < j < a.Length && j < n ==> a[i] <= a[j]
    invariant forall i :: 0 <= i < n ==> forall j :: n <= j < a.Length ==> a[i] <= a[j]
  {
    var mindex, m := n, n;
    while m != a.Length
      invariant n <= mindex < a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    if a[mindex] < a[n] {
      a[mindex], a[n] := a[n], a[mindex];
    }
    n := n + 1;
  }  
}

Error:
'while' in 'while n != a.Length': Error: a postcondition could not be proved on this return path
'multiset(a[..]) == old(multiset(a[..]))' in 'ensures multiset(a[..]) == old(multiset(a[..]))': Related location: this is the postcondition that could not be proved
'a[i]' in 'invariant forall i :: n <= i < m ==> a[mindex] <= a[i]': Error: index out of range
'==' in 'invariant multiset(a[..]) == old(multiset(a[..]))': Error: this loop invariant could not be proved on entry
'==' in 'invariant multiset(a[..]) == old(multiset(a[..]))': Related message: loop invariant violation
'a[m]' in 'if a[m] < a[mindex] {': Error: index out of range
Dafny program verifier finished with 1 verified, 4 errors