method Quotient1() 
{
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= y <= 191 && (x == 0 || x == 27) && (y == 191 || y == 2);
    {
        x, y := x + 27, y - 7;
    }
    assert x == 191 / 7 && y == 191 % 7;
}

Error:
'x == 0 || x == 27' in 'invariant 0 <= y <= 191 && (x == 0 || x == 27) && (y == 191 || y == 2);': Error: this invariant could not be proved to be maintained by the loop
'x == 0 || x == 27' in 'invariant 0 <= y <= 191 && (x == 0 || x == 27) && (y == 191 || y == 2);': Related message: loop invariant violation
'y == 191 || y == 2' in 'invariant 0 <= y <= 191 && (x == 0 || x == 27) && (y == 191 || y == 2);': Error: this invariant could not be proved to be maintained by the loop
'y == 191 || y == 2' in 'invariant 0 <= y <= 191 && (x == 0 || x == 27) && (y == 191 || y == 2);': Related message: loop invariant violation
'x == 191 / 7' in 'assert x == 191 / 7 && y == 191 % 7;': Error: assertion might not hold
Dafny program verifier finished with 0 verified, 3 errors