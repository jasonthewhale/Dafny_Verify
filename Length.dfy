datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
    match xs
    case Nil => 0
    case Cons(_, tail) => 1 + Length(tail)
}

method repeatValue<T>(d: T, n: nat) returns (result: List<T>)
    ensures Length(result) == n
{
    result := Nil;
    var i := 0;
    while i < n
        invariant i <= n
        invariant Length(result) == i
    {
        result := Cons(d, result);
        i := i + 1;
    }
}

method Duplicate<T>(xs: List<T>) returns (result: List<T>)
    ensures Length(result) == 2 * Length(xs)
{
    result := Nil;
    var temp := xs;
    while temp != Nil
        decreases temp
        invariant Length(result) == 2 * (Length(xs) - Length(temp))
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