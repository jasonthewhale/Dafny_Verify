method main(x: int, y: int) returns (x_out: int, y_out: int, n: int)
requires x >= 0
requires y >= 0
requires x == y
ensures y_out == n
{
    x_out := x;
    y_out := y;
    n := 0;

    while (x_out != n)
    invariant x_out >= n
    invariant y_out >= n
    invariant x_out + y_out == x + y
    decreases x_out - n
    {
        x_out := x_out - 1;
        y_out := y_out - 1;
    }
}

Error:
'while' in 'while (x_out != n)': Error: a postcondition could not be proved on this return path
'y_out == n' in 'ensures y_out == n': Related location: this is the postcondition that could not be proved
'==' in 'invariant x_out + y_out == x + y': Error: this invariant could not be proved to be maintained by the loop
'==' in 'invariant x_out + y_out == x + y': Related message: loop invariant violation
Dafny program verifier finished with 0 verified, 2 errors