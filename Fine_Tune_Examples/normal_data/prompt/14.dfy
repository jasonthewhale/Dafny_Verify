method main(m: int) returns (a: int)
    requires m > 0
    ensures a >= -m
    ensures a <= m
{
    a := 0;
    var j: int := 1;

    while (j <= m)
    {
        if (*)
        {
            a := a + 1;
        }
        else
        {
            a := a - 1;
        }

        j := j + 1;
    }
}