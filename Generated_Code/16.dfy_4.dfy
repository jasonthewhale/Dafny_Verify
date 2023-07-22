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
        assert x + y == i + j; // additional assertion to help the verifier
        assert x >= 0 && y >= 0; // additional assertion to help the verifier
    }
}