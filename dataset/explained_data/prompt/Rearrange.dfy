
method rearrange(arr: array<int>, N: int) returns (front: int)
    requires N == arr.Length
    requires forall i :: 0 <= i < arr.Length ==> arr[i] == 0 || arr[i] == 1
    modifies arr
    ensures 0 <= front <= arr.Length
    ensures forall i :: 0 <= i <= front - 1 ==> arr[i] == 0
    ensures forall j :: front <= j <= N - 1 ==> arr[j] == 1
    ensures multiset(arr[..]) == old(multiset(arr[..]))
{   
    front := 0;
    var back := N;
    while(front < back)
    {
        if(arr[front] == 1){
            arr[front], arr[back - 1] := arr[back - 1], arr[front];
            back := back - 1;
        }else{
            front := front + 1;
        }
    }
    return front;
}