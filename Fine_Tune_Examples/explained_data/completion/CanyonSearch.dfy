function Dist(x: int, y: int): nat {
  if x < y then y - x else x - y
}

// Find the pair of numbers, one from each of the two sorted arrays, 
// that have the smallest absolute difference.
method CanyonSearch(a: array<int>, b: array<int>) returns (d: nat)
  // Require two arrays of integers are not empty
  requires a.Length != 0 && b.Length != 0
  // Require two arrays of integers are sorted
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires forall i,j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
  // Ensure the result is the smallest absolute difference 
  // which calculated from elements from these two arrays
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i],b[j])
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= Dist(a[i],b[j])
  {
    // Initialize the smallest absolute difference as the first element of two arrays
    d := Dist(a[0],b[0]);
    var m,n := 0,0;
    while m < a.Length && n < b.Length
      // Ensure d can be calculated from elements from these two arrays
      invariant exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == Dist(a[i],b[j])
      // Ensure d is the smallest absolute difference
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