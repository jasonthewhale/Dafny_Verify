I apologize for the confusion. It seems that the Dafny verifier is not recognizing the List datatype. In that case, we can use a different approach by using a helper function to recursively build the list. Here's the updated code:

```
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat
    decreases xs
{
    match xs
    case Nil => 0
    case Cons(_, tail) => 1 + Length(tail)
}

function BuildList<T>(d: T, n: nat): List<T>
    decreases n
{
    if n == 0 then
        Nil
    else
        Cons(d, BuildList(d, n - 1))
}

method repeatValue<T>(d: T, n: nat) returns (result: List<T>)
    ensures Length(result) == n
{
    result := BuildList(d, n);
}
```