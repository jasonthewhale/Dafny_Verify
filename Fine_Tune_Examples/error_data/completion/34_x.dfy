method main() returns (i: int, x: int, y: int, m: int)
ensures (i != m) || (x == 2*y)
{
    x := 0;
    y := 0;
    i := 0;
    m := 10;

    while(i < m)
        invariant 0 <= i <= m
        invariant x == i
        invariant y == i / 2
    {
		i := i + 1;
		x := x + 1;

		if(x % 2 == 0){
			y := y + 1;
		}
		else{}
	}
}