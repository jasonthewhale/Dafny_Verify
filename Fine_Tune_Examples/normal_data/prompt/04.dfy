method Main1() returns (x: int, y: int)
ensures y > 0
{
    x := -50;
    y := 1;

    while(x < 0)
        decreases (-x)
    {
        x := x + y;
        y := y + 1;
    }
}