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
    invariant k >= 0
    invariant v == 0 || v == 1
    invariant k == i * c1 + (n - i) * c2
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
    assert k > n;
}