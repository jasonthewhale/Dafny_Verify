method main(n: int, flag: int) returns (j: int, b: int)
requires n > 0
ensures (flag != 1) || (j == n)
{
    j := 0;
    b := 0;

    while(b < n)
        invariant 0 <= b <= n
        invariant (flag != 1) || (j == b)
    {
        if(flag == 1){
            j := j + 1;
        }
        else{}
        b := b + 1;
    }
}





// MODULE main
// 	int b;
// 	int j;
// 	int flag;
// 	int n;

// 	assume(j == 0);
// 	assume(n > 0);
// 	assume(b == 0);

// 	while(b < n){
// 		if(flag == 1){
// 			j = j + 1;
// 		}
// 		else{
// 			skip;
// 		}

// 		b = b + 1;
// 	}

// 	assert((flag != 1) || (j == n));
	

// END MODULE