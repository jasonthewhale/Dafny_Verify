method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant forall i :: 0 <= i < n ==> forall j :: n <= j < a.Length ==> a[i] <= a[j]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var mindex, m := n, n;
    while m != a.Length
      invariant n <= mindex < a.Length
      invariant n <= m <= a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
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
'forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]' in 'ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]': Related location: this is the postcondition that could not be proved
'mindex < a.Length' in 'invariant n <= mindex < a.Length': Error: this loop invariant could not be proved on entry
'mindex < a.Length' in 'invariant n <= mindex < a.Length': Related message: loop invariant violation
Dafny program verifier finished with 1 verified, 2 errors