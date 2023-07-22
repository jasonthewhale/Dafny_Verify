method CoincidenceCount(a: array<int>, b: array<int>) returns (c: nat)
    // Requires that the arrays are sorted
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
    requires forall i, j :: 0 <= i < j < b.Length ==> b[i] < b[j]
    // Ensures return value is the number of elements in the intersection of  
    // the elements of a and b
    ensures c == |multiset(a[..]) * multiset(b[..])|
{
    c := 0;
    var m, n := 0, 0;
    while m < a.Length && n < b.Length
        invariant 0 <= m <= a.Length && 0 <= n <= b.Length
        invariant c + |multiset(a[m..]) * multiset(b[n..])| == |multiset(a[..]) * multiset(b[..])|
        decreases a.Length - m + b.Length - n
    {
        if a[m] == b[n] {
            c := c + 1;
            m := m + 1;
            n := n + 1;
        } else if a[m] < b[n] {
            m := m + 1;
        } else {
            n := n + 1;
        }
    }
}
