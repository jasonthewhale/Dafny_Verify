function Dist(x: int, y: int): nat {
  if x < y then y - x else x - y
}

method CanyonSearch(a: array<int>, b: array<int>) returns (d: nat)
  requires a.Length != 0 && b.Length != 0
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires forall i,j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i],b[j])
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i],b[j])
  {
    d := Dist(a[0],b[0]);
    var m,n := 0,0;
    while m < a.Length && n < b.Length
      invariant forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i],b[j]) || (i >= m && j >= n)
      decreases b.Length - n, a.Length - m   
    {
      if Dist(a[m],b[n]) < d {
        d := Dist(a[m],b[n]);
      }
      if a[m] < b[n] {
        m := m + 1;
      } else {
        n := n + 1;
        m := 0;
      }
    }
  }

Error:
'while' in 'while m < a.Length && n < b.Length': Error: a postcondition could not be proved on this return path
'exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i],b[j])' in 'ensures exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i],b[j])': Related location: this is the postcondition that could not be proved
Dafny program verifier finished with 2 verified, 1 error