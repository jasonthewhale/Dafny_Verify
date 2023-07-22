method Main1() returns (x: int, y: int)
ensures y > 0
{
    x := -50;
    y := 1;

    while(x < 0)
        decreases (-x)
        invariant -50 <= x <= y
        invariant 0 < y <= x + 51
    {
        x := x + y;
        y := y + 1;
    }
}