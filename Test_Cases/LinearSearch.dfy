method LinearSearch0<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
{
    n := 0;
    while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i: int :: 0 <= i < n ==> !P(a[i])
    {
        if P(a[n]) {
            return;
        }
        n := n + 1;
    }
}

method LinearSearch1<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
    ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !P(a[i])

method LinearSearch2<T>(a: array<T>, P: T -> bool) returns (n: int)
 ensures 0 <= n <= a.Length
 ensures n == a.Length || P(a[n])
 ensures forall i :: 0 <= i < n ==> !P(a[i])
