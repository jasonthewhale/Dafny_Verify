function sorted(a: array<int>, fromIndex: int, toIndex: int): bool
reads a
  requires fromIndex >= 0 && toIndex <= a.Length && fromIndex <= toIndex
{
  forall i, j :: fromIndex <= i <= j < toIndex ==> a[i] <= a[j]
}

method merge(a: array<int>, start: int, mid: int, n: int) returns (b: array<int>)
  requires n <= a.Length;
  requires 0 <= start;
  requires start <= mid;
  requires mid <= n;
  requires sorted(a, mid, n);
  ensures b.Length == a.Length;
{
  var i, l, r: int;
  b := new int[a.Length];

  i, l, r := start, start, mid;
  
  while (i < n)
    invariant start <= l <= mid;
    invariant mid <= r <= n;
    invariant forall j, k :: l <= j && j < k && k < mid ==> a[j] <= a[k];
    invariant forall j, k :: r <= j && j < k && k < n ==> a[j] <= a[k];
    invariant r < n ==> forall j :: start <= j && j < i ==> b[j] <= a[r];
    invariant sorted(b, start, i);
  {
    if r >= n || (l < mid && a[l] < a[r]) {
      b[i] := a[l];
      l := l + 1;
    } else {
      b[i] := a[r];
      r := r + 1;
    }
    i := i + 1;
  }
}

Error:
'l <= mid' in 'invariant start <= l <= mid;': Error: this invariant could not be proved to be maintained by the loop
'l <= mid' in 'invariant start <= l <= mid;': Related message: loop invariant violation
'forall' in 'invariant forall j, k :: l <= j && j < k && k < mid ==> a[j] <= a[k];': Error: this loop invariant could not be proved on entry
'forall' in 'invariant forall j, k :: l <= j && j < k && k < mid ==> a[j] <= a[k];': Related message: loop invariant violation
'b[j]' in 'invariant r < n ==> forall j :: start <= j && j < i ==> b[j] <= a[r];': Error: index out of range
'sorted(b, start, i)' in 'invariant sorted(b, start, i);': Error: function precondition might not hold
'toIndex <= a.Length' in 'requires fromIndex >= 0 && toIndex <= a.Length && fromIndex <= toIndex': Related location
'a[l]' in 'b[i] := a[l];': Error: index out of range
Dafny program verifier finished with 2 verified, 5 errors