method Max(a: array<nat>) returns (m: int)
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
    m := 0;
    var n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> a[i] <= m
        invariant (m == 0 && n == 0) || exists i :: 0 <= i < n && m == a[i]
    {
        if m < a[n] {
            m := a[n]; 
        }
        n := n + 1; 
    }
}