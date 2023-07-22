method main(k: int, b: int, i: int, j: int, n: int) returns (i_out: int, j_out: int, n_out: int)
requires k > 0
requires i == j
requires n == 0
ensures i_out == j_out
{
    var i_local := i;
    var j_local := j;
    var n_local := n;
    var b_local := b;

    while (n_local < 2 * k)
    invariant 0 <= n_local <= 2 * k
    invariant i_local == j_local || i_local == j_local + 1
    decreases 2 * k - n_local
    {
        if (b_local == 1) {
            i_local := i_local + 1;
            b_local := 0;
        }
        else {
            j_local := j_local + 1;
            b_local := 1;
        }

        n_local := n_local + 1;
    }
    
    i_out := i_local;
    j_out := j_local;
    n_out := n_local;
}


// MODULE main
// 	int k;
// 	int b;
// 	int i;
// 	int j;
// 	int n;

// 	assume(k > 0);
// 	assume(i == j);
// 	assume(n == 0);

// 	while(n < 2*k){
// 		if(b == 1){
// 			i = i + 1;
// 			b = 0;
// 		}
// 		else{
// 			j = j + 1;
// 			b = 1;
// 		}

// 		n = n + 1;
// 	}

// 	assert(i == j);	

// END MODULE