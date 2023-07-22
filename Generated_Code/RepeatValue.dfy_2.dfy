import Dafny.Stdlib.List;

method repeatValue<T>(d: T, n: nat) returns (result: List<T>)
    ensures Length(result) == n
{
    result := Nil;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant Length(result) == i
    {
        result := Cons(d, result);
        i := i + 1;
    }
}
