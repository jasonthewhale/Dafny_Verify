method main(m: int, n: int) returns (x: int, y: int)
requires m >= 0
requires n >= 0
requires m < n
ensures y == n
{
    x := 0;
    y := m;

    while (x < n)
        invariant 0 <= x <= n
        invariant m <= y <= n
        invariant y == m + (if x > m then x - m else 0)
    {
        x := x + 1;
        if (x > m) 
        {
            y := y + 1;
        }
        else 
        {}
    }
}





// MODULE main
//    	int n;
// 	int m;
// 	int x;
// 	int y;

// 	assume(n >= 0);
// 	assume(m >= 0);
// 	assume(m < n);
// 	assume(x == 0);
// 	assume(y == m);

// 	while(x < n){
// 		x = x + 1;
		
// 		if(x > m){
// 			y = y + 1;
// 		}
// 		else{
// 			skip;
// 		}
// 	}

// 	assert(y == n);

// END MODULE