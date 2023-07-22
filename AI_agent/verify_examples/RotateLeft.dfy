method RotateLeft(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
    ensures a[a.Length -1] == old(a[0])
{
    var n := 0;
    while n != a.Length - 1
        invariant 0 <= n <= a.Length - 1
        invariant forall i :: 0 <= i < n ==> a[i] == old(a[i+1]) 
        invariant a[n] == old(a[0])
        invariant forall i :: n < i <= a.Length-1 ==> a[i] == old(a[i])
    {
        a[n], a[n+1] := a[n+1], a[n];
        n := n + 1; 
    }
}