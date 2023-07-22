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
        invariant Length(result) == i
    {
        result := Cons(d, result);
        i := i + 1;
    }
}

Error:
'while' in 'while i < n': Error: a postcondition could not be proved on this return path
'Length(result) == n' in 'ensures Length(result) == n': Related location: this is the postcondition that could not be proved
Dafny program verifier finished with 1 verified, 1 error