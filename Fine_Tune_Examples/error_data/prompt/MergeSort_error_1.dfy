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
  requires sorted(a, start, mid);
  requires sorted(a, mid, n);
  ensures b.Length == a.Length;
  ensures sorted(b, start, n);
{
  var i, l, r: int;
  b := new int[a.Length];

  i, l, r := start, start, mid;
  
  while (i < n)
    invariant start <= i <= n;
    invariant start <= l <= mid;
    invariant mid <= r <= n;
    invariant sorted(a, start, l);
    invariant sorted(a, r, n);
    invariant forall k :: start <= k < i ==> (r >= n || (l < mid && a[l] < a[r]) ==> b[k] == a[l]) && (!(r >= n || (l < mid && a[l] < a[r])) ==> b[k] == a[r]);
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
'forall' in 'invariant forall k :: start <= k < i ==> (r >= n || (l < mid && a[l] < a[r]) ==> b[k] == a[l]) && (!(r >= n || (l < mid && a[l] < a[r])) ==> b[k] == a[r]);': Error: this invariant could not be proved to be maintained by the loop
'forall' in 'invariant forall k :: start <= k < i ==> (r >= n || (l < mid && a[l] < a[r]) ==> b[k] == a[l]) && (!(r >= n || (l < mid && a[l] < a[r])) ==> b[k] == a[r]);': Related message: loop invariant violation
'a[l]' in 'invariant forall k :: start <= k < i ==> (r >= n || (l < mid && a[l] < a[r]) ==> b[k] == a[l]) && (!(r >= n || (l < mid && a[l] < a[r])) ==> b[k] == a[r]);': Error: index out of range
'a[l]' in 'b[i] := a[l];': Error: index out of range
Dafny program verifier finished with 2 verified, 4 errors