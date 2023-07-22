import ListModule from "ListModule";

method Duplicate<T>(xs: ListModule.List<T>) returns (result: ListModule.List<T>)
    ensures ListModule.Length(result) == 2 * ListModule.Length(xs)
{
    result := ListModule.Nil;
    var temp := xs;
    while temp != ListModule.Nil
        invariant ListModule.Length(result) + ListModule.Length(temp) == 2 * ListModule.Length(xs)
        decreases temp
    {
        var h: T;
        var t: ListModule.List<T>;
        match temp
        case ListModule.Nil => 
        case ListModule.Cons(h, t) => {
            result := ListModule.Cons(h, ListModule.Cons(h, result));
            temp := t;
        }
    }
}