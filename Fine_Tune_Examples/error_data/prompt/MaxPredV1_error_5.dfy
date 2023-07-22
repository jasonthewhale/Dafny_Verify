function contains(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  exists j :: 0 <= j < n && a[j] == v
}

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  forall j :: 0 <= j < n ==> a[j] <= v
}

method max(a: array<int>, n: int) returns (max: int)
  requires n > 0;
  requires n <= a.Length;
  ensures exists j :: 0 <= j < n && a[j] == max;
  ensures forall j :: 0 <= j < n ==> a[j] <= max;
{
  var i: int;
  max := a[0];
  i := 1;

  while i < n
    invariant contains(max, a, i);
    invariant upper_bound(max, a, i);
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}

Error:
'while' in 'while i < n': Error: a postcondition could not be proved on this return path
'exists j :: 0 <= j < n && a[j] == max' in 'ensures exists j :: 0 <= j < n && a[j] == max;': Related location: this is the postcondition that could not be proved
'contains(max, a, i)' in 'invariant contains(max, a, i);': Error: function precondition might not hold
'n <= a.Length' in 'requires n <= a.Length': Related location
'upper_bound(max, a, i)' in 'invariant upper_bound(max, a, i);': Error: function precondition might not hold
'n <= a.Length' in 'requires n <= a.Length': Related location
Dafny program verifier finished with 3 verified, 3 errors