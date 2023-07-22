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

Error:
'x == 27' in 'invariant 0 <= y <= 191 && x == 27 && y == 2;': Error: this loop invariant could not be proved on entry
'x == 27' in 'invariant 0 <= y <= 191 && x == 27 && y == 2;': Related message: loop invariant violation
Dafny program verifier finished with 0 verified, 1 error