method Main1() returns (x: int, y: int)
ensures y > 0
{
    x := -50;
    y := 1;

    while(x < 0)
        decreases (-x)
        invariant x <= 0 && y > 0
    {
        x := x + y;
        y := y + 1;
    }
}

Error:
'x <= 0' in 'invariant x <= 0 && y > 0': Error: this invariant could not be proved to be maintained by the loop
'x <= 0' in 'invariant x <= 0 && y > 0': Related message: loop invariant violation
Dafny program verifier finished with 0 verified, 1 error