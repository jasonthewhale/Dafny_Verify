method main(n: int, k: int) returns (i: int, j :int)
requires n ==1 || n == 2
ensures (n != 1) || (i == j)
{
    i := 0;
    j := 0;
    while(i <= k)
        invariant i >= 0 && j == i * n;
    {
        i := i + 1;
        j := j + n;
    }
}




// MODULE main
// 	int i;
// 	int j;
// 	int n;
// 	int k;

// 	assume(n == 1 || n == 2);
// 	assume(i == 0);
// 	assume(j == 0);

// 	while(i <= k){
// 		i = i + 1;
// 		j = j + n;
// 	}

// 	assert((n != 1) || (i == j));	

// END MODULE