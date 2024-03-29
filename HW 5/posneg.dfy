function numPos(a: seq<int>, i: int, j: int) : int
requires i >= 0 && j <= |a|
{
    if i >= j then 0
    else if a[j - 1] > 0 then 1 + numPos(a, i, j - 1) else numPos(a, i, j - 1)
}

function numNeg(a: seq<int>, i: int, j: int) : int
requires i >= 0 && j <= |a|
{
    if i >= j then 0
    else if a[j - 1] < 0 then 1 + numNeg(a, i, j - 1) else numNeg(a, i, j - 1)
}

method eqPosNeg (a: seq<int>) returns (e: bool)
ensures e ==> numPos(a, 0, |a|) == numNeg(a, 0, |a|)
{
    var i := 0;
    var npos := 0;
    var nneg := 0;
    while (i < |a|)
    invariant (i <= |a| && 0 <= i && npos == numPos(a, 0, i) && nneg == numNeg(a, 0, i))
    {
        if a[i] > 0 { npos := npos + 1; }
        if a[i] < 0 { nneg := nneg + 1; }
        i := i + 1;
    }
    e := npos == nneg;
}
