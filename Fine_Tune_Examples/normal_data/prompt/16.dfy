method main(i: int, j: int) returns (x: int, y: int)
requires i >= 0 && j >= 0
ensures (i != j) || (y == 0)
{
    x := i;
    y := j;

    while(x != 0)
    {
        x := x - 1;
        y := y - 1;
    }
}