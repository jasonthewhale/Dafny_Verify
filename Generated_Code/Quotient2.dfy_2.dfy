method Quotient1() 
{
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= y <= 191 && x == 27 && y == 2;
    {
        x, y := 27, 2;
    }
    assert x == 191 / 7 && y == 191 % 7;
}
