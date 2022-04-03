method findFirstGreater (a: seq<int>, x: int) returns (i : int)
ensures (0 <= i < |a| && forall j :: (0 <= j < i) ==> a[j] <= x && a[i] > x) || i == |a|
{
    i := 0;
    while (i < |a| && a[i] <= x)
    invariant 0 <= i <= |a| && forall j :: (0 <= j < i) ==> a[j] <= x
    {
        i := i + 1;
    }
}

// exists n :: n in a && n >= x && a[i] == n
// forall j :: (0 <= j < i) ==> a[j] <= x
