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
        invariant forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> (a[i,j] == key || (i > m && j < n))
    {
        if a[m,n] < key {
            m := m + 1;
        } else {
            n := n - 1;
        }
    }
}

Error:
'forall' in 'invariant forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> (a[i,j] == key || (i > m && j < n))': Error: this loop invariant could not be proved on entry
'forall' in 'invariant forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> (a[i,j] == key || (i > m && j < n))': Related message: loop invariant violation
Dafny program verifier finished with 1 verified, 1 error