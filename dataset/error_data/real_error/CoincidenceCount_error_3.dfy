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
        // Loop invariant: c is the number of elements in the intersection of a[..m] and b[..n]
        invariant c == |multiset(a[..m]) * multiset(b[..n])|
        invariant 0 <= m <= a.Length
        invariant 0 <= n <= b.Length
        invariant forall k :: 0 <= k < m ==> a[k] <= b[n]
        invariant forall k :: 0 <= k < n ==> b[k] <= a[m]
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

Error:
'{': Error: a postcondition could not be proved on this return path
'ensures c == |multiset(a[..]) * multiset(b[..])|': Related location: this is the postcondition that could not be proved
'invariant c == |multiset(a[..m]) * multiset(b[..n])|': Error: upper bound below lower bound or above length of array
'invariant c == |multiset(a[..m]) * multiset(b[..n])|': Error: upper bound below lower bound or above length of array
'b[n]': Error: index out of range
'a[m]': Error: index out of range

Dafny program verifier finished with 1 verified, 5 errors