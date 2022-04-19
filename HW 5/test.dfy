function method power(A:int, N:nat):int
{
	if (N==0) then 1 else A * power(A,N-1)
}

method findFirstGreater (a: seq<int>, i: int, k: nat) returns (x : int)
requires |a| >= 1 && i == 0 && a[i] >= 1
ensures x == power(2, k) && x <= a[i] && a[i] < power(2, k + 1)
{
    x := 1;
    var k := 0;
    while(x * 2 <= a[i])
    invariant x == power(2, k) && x <= a[i]
    decreases a[i] - x * 2
    {
        k := k + 1;
        x := x * 2;
    }
}

// exists n :: n in a && n >= x && a[i] == n
// forall j :: (0 <= j < i) ==> a[j] <= x
