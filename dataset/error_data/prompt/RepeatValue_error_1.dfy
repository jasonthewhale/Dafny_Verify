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

Error:
'method repeatValue<T>(d: T, n: nat) returns (result: List<T>)': Error: Type or type parameter is not declared in this scope: List (did you forget to qualify a name or declare a module import 'opened'? names in outer modules are not visible in nested modules)

1 resolution/type errors detected in RepeatValue.dfy_1.dfy