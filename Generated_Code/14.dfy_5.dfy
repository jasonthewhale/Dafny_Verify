method main(m: int) returns (a: int)
    requires m > 0
    ensures a >= -m
    ensures a <= m
{
    a := 0;
    var j: int := 1;

    while (j <= m)
        invariant 1 <= j <= m + 1
        invariant -m - 1 <= a <= m + 1
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

    return a;
}