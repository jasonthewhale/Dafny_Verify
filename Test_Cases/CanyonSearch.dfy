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
      invariant exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i],b[j])
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


  method CanyonSearch2(a: array<int>, b: array<int>) returns (d: nat)
  requires a.Length != 0 && b.Length != 0
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires forall i,j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i],b[j])
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i],b[j])
{
  d := Dist(a[0],b[0]);
  var m,n := 0,0;
  while m < a.Length && n < b.Length
    invariant 0 <= m <= a.Length
    invariant 0 <= n <= b.Length
    invariant forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i],b[j]) || (i >= m && j >= n)
    invariant exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i],b[j])
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


  method CanyonSearch1(a: array<int>, b: array<int>) returns (d: nat)
  requires a.Length != 0 && b.Length != 0
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires forall i,j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i],b[j])
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i],b[j])
  {
    d := Dist(a[0],b[0]);
    var m, n := 0, 0;
    var i_min, j_min := 0, 0;  // ghost variables
    while m < a.Length && n < b.Length
      invariant forall i, j :: 0 <= i < m && 0 <= j <= n ==> d <= Dist(a[i],b[j])
      invariant forall i, j :: 0 <= i <= m && 0 <= j < n ==> d <= Dist(a[i],b[j])
      invariant 0 <= i_min <= m
      invariant 0 <= j_min <= n
      invariant d == Dist(a[i_min], b[j_min])
      invariant 0 <= m <= a.Length
      invariant 0 <= n <= b.Length
      decreases a.Length - m + b.Length - n
    {
      if Dist(a[m],b[n]) < d {
        d := Dist(a[m],b[n]);
        i_min, j_min := m, n;  // update the indices when we find a smaller distance
      }
      if a[m] < b[n] {
        m := m + 1;
      } else {
        n := n + 1;
      }
    }
  }

