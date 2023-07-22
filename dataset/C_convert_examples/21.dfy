method main(n: int) returns (i: int, v: int, k: int, c1: int, c2: int)
requires n > 0 && n < 10
ensures k > n
{
    i := 0;
    k := 0;
    v := 0;
    c1 := 4000;
    c2 := 2000;
    while(i < n)
        invariant 0 <= i <= n
        invariant i * c2 <= k <= i * c1;
    {
        i := i + 1;
        
        if(*){
            v := 0;		
        }
        else{
            v := 1;
        }

        if(v == 0){
            k := k + c1;
        }
        else{
            k := k + c2;
        }
    }
}



// MODULE main
// 	int i;
// 	int j;
// 	int k;
// 	int c1;
// 	int c2;
// 	int n;
// 	int v;

// 	assume(n > 0 && n < 10);
// 	assume(k == 0);
// 	assume(i == 0);
// 	assume(c1 == 4000);
// 	assume(c2 == 2000);

// 	while(i < n){
// 		i = i + 1;
		
// 		if(*){
// 			v = 0;		
// 		}
// 		else{
// 			v = 1;
// 		}

// 		if(v == 0){
// 			k = k + c1;
// 		}
// 		else{
// 			k = k + c2;
// 		}
// 	}

// 	assert(k > n);	

// END MODULE