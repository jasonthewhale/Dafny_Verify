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