method Duplicate<T>(xs: List<T>) returns (result: List<T>)
    ensures Length(result) == 2 * Length(xs)
{
    result := Nil;
    var temp := xs;
    while temp != Nil
        invariant Length(result) + Length(temp) == 2 * Length(xs)
        decreases temp
    {
        var h: T;
        var t: List<T>;
        match temp
        case Nil => 
        case Cons(h, t) => {
            result := Cons(h, Cons(h, result));
            temp := t;
        }
    }
}

Error:
'method Duplicate<T>(xs: List<T>) returns (result: List<T>)': Error: Type or type parameter is not declared in this scope: List (did you forget to qualify a name or declare a module import 'opened'? names in outer modules are not visible in nested modules)
'method Duplicate<T>(xs: List<T>) returns (result: List<T>)': Error: Type or type parameter is not declared in this scope: List (did you forget to qualify a name or declare a module import 'opened'? names in outer modules are not visible in nested modules)

2 resolution/type errors detected in DuplicateList.dfy_1.dfy