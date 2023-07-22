method main(i: int, j: int) returns (x: int, y: int)
requires i >= 0 && j >= 0
ensures (i != j) || (y == 0)
{
    x := i;
    y := j;

    while(x != 0)
    invariant x >= 0;
    invariant y == j - (i - x);
    {
        x := x - 1;
        y := y - 1;
    }
}


// MODULE main
// 	int x;
// 	int y;
// 	int i;
// 	int j;

// 	assume(x == i);
// 	assume(y == j);

// 	while(x != 0){
// 		x = x - 1;
// 		y = y - 1;
// 	}

// 	assert((i != j) || (y == 0));	

// END MODULE