method Quotient()
{
    var x, y := 0, 191;
    while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
    {
        y := y - 7;
        x := x + 1;
    }
    assert x == 191 / 7 && y == 191 % 7;
}