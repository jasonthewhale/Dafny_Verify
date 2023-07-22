method SlopeSearch(a: array2<int>, key: int) returns (m: int, n: int)
    requires forall i, j, j1 ::
        0 <= i < a.Length0 && 0 <= j < j1 < a.Length1 ==>
        a[i,j] <= a[i,j1]
    requires forall i, i1, j ::
        0 <= i < i1 < a.Length0 && 0 <= j < a.Length1 ==>
        a[i,j] <= a[i1,j]
    requires exists i, j ::
        0 <= i < a.Length0 && 0 <= j < a.Length1 && a[i,j] == key
    ensures 0 <= m < a.Length0 && 0 <= n < a.Length1
    ensures a[m,n] == key
{
    m, n := 0, a.Length1 - 1;
    while a[m,n] != key
        decreases a.Length0 - m + n
        invariant 0 <= m < a.Length0 && 0 <= n < a.Length1
        invariant exists i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 && a[i,j] == key
    {
        if a[m,n] < key {
            m := m + 1;
        } else {
            n := n - 1;
        }
    }
}

Error:
'm < a.Length0' in 'invariant 0 <= m < a.Length0 && 0 <= n < a.Length1': Error: this invariant could not be proved to be maintained by the loop
'm < a.Length0' in 'invariant 0 <= m < a.Length0 && 0 <= n < a.Length1': Related message: loop invariant violation
'0 <= n' in 'invariant 0 <= m < a.Length0 && 0 <= n < a.Length1': Error: this invariant could not be proved to be maintained by the loop
'0 <= n' in 'invariant 0 <= m < a.Length0 && 0 <= n < a.Length1': Related message: loop invariant violation
Dafny program verifier finished with 1 verified, 2 errors