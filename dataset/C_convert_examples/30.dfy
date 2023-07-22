method main(n: int) returns (c: int, i: int)
requires n > 0
ensures c >= 0
{
    c := 0;
    i := 0;
    while(i < n)
        invariant 0 <= i <= n
        invariant c == i * (i - 1) / 2
    {
        c := c + i;
        i := i + 1;
    }
}





// MODULE main
// 	int i;
// 	int c;
// 	int n;

// 	assume(i == 0);
// 	assume(c == 0);
// 	assume(n > 0);

// 	while(i < n){
// 		c = c + i;
// 		i = i + 1;
// 	}

// 	assert(c >= 0);	

// END MODULE