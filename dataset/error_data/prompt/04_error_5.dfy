method Main1() returns (x: int, y: int)
ensures y > 0
{
    x := -50;
    y := 1;

    while(x < 0)
        decreases (-x)
        invariant x <= 0 && y > 0 && x + y <= 3
    {
        x := x + y;
        y := y + 1;
    }
}

Error:
'x <= 0' in 'invariant x <= 0 && y > 0 && x + y <= 3': Error: this invariant could not be proved to be maintained by the loop
'x <= 0' in 'invariant x <= 0 && y > 0 && x + y <= 3': Related message: loop invariant violation
'x + y <= 3' in 'invariant x <= 0 && y > 0 && x + y <= 3': Error: this invariant could not be proved to be maintained by the loop
'x + y <= 3' in 'invariant x <= 0 && y > 0 && x + y <= 3': Related message: loop invariant violation
Dafny program verifier finished with 0 verified, 2 errors