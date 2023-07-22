method main(n: int, k: int) returns (i :int, j: int)
    requires n >= 0
    requires k == 1 || k >= 0
    ensures k + i + j >= 2 * n
{
    i := 0;
    j := 0;
    while(i < n)
        invariant 0 <= i <= n
        invariant j == i * (i + 1) / 2
    {
        i := i + 1;
        j := j + i;
    }
}








// MODULE main
// 	int n;
// 	int k;
// 	int i;
// 	int j;

// 	assume(j == 0);
// 	assume(n >= 0);
// 	assume(i == 0);
// 	assume(k == 1 || k >= 0);

// 	while(i <= n){
// 		i = i + 1;
// 		j = j + i;
// 	}

// 	assert(k + i + j > 2 * n);
	

// END MODULE