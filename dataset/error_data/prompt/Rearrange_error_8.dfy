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
        invariant 0 <= front <= back <= N
        invariant forall i :: 0 <= i < arr.Length ==> arr[i] == 0 || arr[i] == 1
        invariant forall i :: 0 <= i <= front - 1 ==> arr[i] == 0
        invariant forall j :: back <= j < N ==> arr[j] == 1
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

Error:
'return' in 'return front;': Error: a postcondition could not be proved on this return path
'multiset(arr[..]) == old(multiset(arr[..]))' in 'ensures multiset(arr[..]) == old(multiset(arr[..]))': Related location: this is the postcondition that could not be proved
Dafny program verifier finished with 1 verified, 1 error