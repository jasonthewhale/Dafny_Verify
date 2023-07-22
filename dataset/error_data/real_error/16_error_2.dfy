method main(i: int, j: int) returns (x: int, y: int)
requires i >= 0 && j >= 0
ensures (i != j) || (y == 0)
{
    x := i;
    y := j;

    while(x != 0)
    invariant x >= 0 && y >= 0 && x + y == i + j
    decreases x
    {
        x := x - 1;
        y := y - 1;
    }
}

Error:
'{': Error: a postcondition could not be proved on this return path
'ensures (i != j) || (y == 0)': Related location: this is the postcondition that could not be proved
'invariant x >= 0 && y >= 0 && x + y == i + j': Error: this invariant could not be proved to be maintained by the loop
'invariant x >= 0 && y >= 0 && x + y == i + j': Related message: loop invariant violation
'invariant x >= 0 && y >= 0 && x + y == i + j': Error: this invariant could not be proved to be maintained by the loop
'invariant x >= 0 && y >= 0 && x + y == i + j': Related message: loop invariant violation

Dafny program verifier finished with 0 verified, 3 errors