method main(n: int) returns(x: int, m: int)
requires n > 0
ensures (n <= 0) || (0 <= m && m < n)
{
    x := 0;
    m := 0;

    while(x < n)
        invariant 0 <= x <= n
        invariant 0 <= m < n
    {
        if(*)
        {
            m := x;
        }
        else{}
        x := x + 1;
    }
}






// MODULE main
// 	int x;
// 	int m;
// 	int n;

// 	assume(x == 0);
// 	assume(m == 0);
// 	assume(n > 0);

// 	while(x < n){
// 		if(*){
// 			m = x;		
// 		}
// 		else{
// 			skip;
// 		}

// 		x = x + 1;
// 	}

// 	assert((n <= 0) || (0 <= m && m < n));	

// END MODULE