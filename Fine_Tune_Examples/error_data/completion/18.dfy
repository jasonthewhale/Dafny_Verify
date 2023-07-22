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