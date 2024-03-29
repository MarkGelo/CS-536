function arrsum (a: seq<int>, i: int, j: int) : int
requires i >= 0 && j <= |a|
decreases (j - i) 
  { if j <= i then 0 else a[j-1] + arrsum(a, i, j - 1)}

method sumArray (a: seq<int>) returns (s: int)
ensures s == arrsum(a, 0, |a|)
{
    var i := 0;
    s := 0;
    while (i < |a|)
    invariant (i <= |a| && i >= 0 && s == arrsum(a, 0, i))
    {
        s := s + a[i];
        i := i + 1;
    }
}

