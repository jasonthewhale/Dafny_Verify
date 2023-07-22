method main() returns (t1: int, t2: int, x: int, y: int)
ensures y >= 1
{
    x := 1;
    y := 1;
    t1 := 0;
    t2 := 0;

    while(x <= 100000)
        invariant x >= 1 && y >= 1 && t1 >= 0 && t2 >= 0 && t1 == x - y && t2 == x - y && x == t1 + t2 && y == t1 + t2 && x >= y && y >= 1
    {
        t1 := x;
        t2 := y;
        x := t1 + t2;
        y := t1 + t2;
    }
}

Error:
'invariant x >= 1 && y >= 1 && t1 >= 0 && t2 >= 0 && t1 == x - y && t2 == x - y && x == t1 + t2 && y == t1 + t2 && x >= y && y >= 1': Error: this loop invariant could not be proved on entry
'invariant x >= 1 && y >= 1 && t1 >= 0 && t2 >= 0 && t1 == x - y && t2 == x - y && x == t1 + t2 && y == t1 + t2 && x >= y && y >= 1': Related message: loop invariant violation

Dafny program verifier finished with 0 verified, 1 error