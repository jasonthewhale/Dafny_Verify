method LinearSearch0<T>(a: array<T>, P: T -> bool) returns (n: int) 	
	ensures 0 <= n <= a.Length 
	ensures n == a.Length || P(a[n])
{ 
	n := 0; 
	while n != a.Length 
		invariant 0 <= n <= a.Length 
		invariant forall k :: 0 <= k < n ==> !P(a[k])
	{  
		if P(a[n]) { return; } 
		n := n + 1;   
	}
}

predicate P(n: int) {
	n % 2 == 0
} 

method TestLinearSearch() {
	var a := new int[3][1,2,4];
	var n := LinearSearch2<int>(a,P);
	assert P(a[1]);
	assert n == 1;
}

method LinearSearch1<T>(a: array<T>, P: T -> bool) returns (n: int) 	
	ensures 0 <= n <= a.Length 
	ensures n == a.Length || P(a[n])
	ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
{ 
	n := 0; 
	while n != a.Length 
		invariant 0 <= n <= a.Length
		invariant forall i :: 0 <= i < n ==> !P(a[i])
		// invariant 0 <= n <= a.Length
		// invariant forall i :: 0 <= i < n ==> !P(a[i])
	{  
	    if P(a[n]) { return; } 
		n := n + 1;   
	}
}

method LinearSearch2<T>(a: array<T>, P: T -> bool) returns (n: int) 	
	ensures 0 <= n <= a.Length 
	ensures n == a.Length || P(a[n])
	ensures forall i :: 0 <= i < n ==> !P(a[i])
{ 
	n := 0; 
	while n != a.Length 
		invariant 0 <= n <= a.Length
		invariant forall i :: 0 <= i < n ==> !P(a[i])
	{  
	    if P(a[n]) { return; } 
		n := n + 1;   
	}
}

method LinearSearch3<T>(a: array<T>, P: T -> bool) returns (n: int) 	
	requires exists i :: 0 <= i < a.Length && P(a[i])
	ensures 0 <= n < a.Length && P(a[n])
{ 
	n := 0; 
	while true
		invariant 0 <= n < a.Length 
		invariant exists i :: n <= i < a.Length && P(a[i])
		// invariant 0 <= n <= a.Length
		// invariant forall k :: 0 <= k < n ==> !P(a[k])
		decreases a.Length - n
	{  
	    if P(a[n]) { return; } 
		n := n + 1;   
	}
}

method LinearSearch4<T(==)>(a: array<T>, P: T) returns (n: int) 	
	ensures 0 <= n <= a.Length 
	ensures n == a.Length || a[n]==P
	ensures forall i :: 0 <= i < n ==> a[i] != P
{ 
	n := 0; 
	while n != a.Length 
		invariant 0 <= n <= a.Length 
		invariant forall i :: 0 <= i < n ==> a[i] != P
		// invariant 0 <= n <= a.Length
		// invariant forall i :: 0 <= i < n ==> a[i] != P
	{  
	    if a[n] == P { return; } 
		n := n + 1;   
	}
}

predicate Q(n: int, len: int)
{
  n < len
}

// method LinearSearch0<T>(a: array<T>, P: T -> bool) returns (n: int) 	
// 	ensures 0 <= n <= a.Length 
// 	ensures n == a.Length || P(a[n])
// { 
// 	n := 0; 
// 	while n != a.Length 
// 		invariant 0 <= n <= a.Length 
// 		invariant forall k :: 0 <= k < n ==> !P(a[k])
// 	{  
// 		if P(a[n]) { return; } 
// 		n := n + 1;   
// 	}
// }

method LinearSearch_0(a: array<int>, Q: (int, int) -> bool) returns (n: int)
	ensures n < a.Length
	ensures forall i :: 0 <= i < n ==> !Q(a[i], a.Length)
{
	n := 0;
	while n != a.Length
		invariant 0 <= n <= a.Length
		invariant forall i :: 0 <= i < n ==> !Q(a[i], a.Length)
	{
		if Q(a[n], a.Length) { return; }
		n := n + 1;
	}
	n := -1;
}

method LinearSearch(a: array<int>, len: int, Q: (int, int) -> bool) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || Q(a[n], len)
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !Q(a[i], len)
{
  n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> !Q(a[i], len)
  {
    if Q(a[n], len) { return; }
    n := n + 1;
  }
}
