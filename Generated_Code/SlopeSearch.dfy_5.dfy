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
        invariant forall i, j ::
            (0 <= i < m && 0 <= j < a.Length1) ==> (a[i,j] < key)
            && forall i1, j1 ::
                (m <= i1 < a.Length0 && 0 <= j1 < n) ==> (a[i1,j1] > key)
    {
        if a[m,n] < key {
            m := m + 1;
        } else {
            n := n - 1;
        }
    }
}