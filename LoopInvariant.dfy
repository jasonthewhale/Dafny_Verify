method UpWhileLess(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := 0;
    while i < N 
    invariant 0 <= i <= N
    decreases N - i
    {
        i := i + 1;
    }
}


method UpWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := 0;
    while i != N
    invariant 0 <= i <= N
    decreases N - i
    {
        i := i + 1;
    }
}


method DownWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while i != 0 
    invariant 0 <= i <= N
    decreases i
    {
        i := i - 1;
    }
}


method DownWhileGreater(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while 0 < i 
    invariant 0 <= i <= N
    decreases i
    {
        i := i - 1;
    }
}



r, N := 0, 104;
while (r+1)*(r+1) <= N
invariant 0 <= r && r*r <= N
assert 0 <= r && r*r <= N < (r+1)*(r+1)