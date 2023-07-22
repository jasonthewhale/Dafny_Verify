method Main1() returns (x: int, y: int)
ensures y > 0
{
    x := -50;
    y := 1;

    while(x < 0)
        decreases (-x)
        invariant x <= 0 && y > 0 && x + y <= 2
    {
        x := x + y;
        y := y + 1;
    }
}

Error:
'invariant x <= 0 && y > 0 && x + y <= 2': Error: this invariant could not be proved to be maintained by the loop
'invariant x <= 0 && y > 0 && x + y <= 2': Related message: loop invariant violation
'invariant x <= 0 && y > 0 && x + y <= 2': Error: this invariant could not be proved to be maintained by the loop
'invariant x <= 0 && y > 0 && x + y <= 2': Related message: loop invariant violation

Dafny program verifier finished with 0 verified, 2 errors