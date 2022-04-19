method findFirstGreater (a: seq<int>, x: int) returns (i : int)
ensures (i >= 0 && i <= |a| && (i < |a| ==> a[i] > x) && 
        (forall j : int :: (j >= 0) && (j < i) ==> a[j] <= x))
{
    i := 0;
    while (i < |a| && a[i] <= x)
    invariant (i >= 0 && i <= |a| && 
       (forall j : int :: (j >= 0) && (j < i) ==> a[j] <= x))
    {
        i := i + 1;
    }
}
