// MODULE main
// 	int x;
// 	int y;

// 	assume(x == -50);

// 	while(x < 0){
// 		x = x + y;
// 		y = y + 1;
// 	}

// 	assert(y > 0);

// END MODULE


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