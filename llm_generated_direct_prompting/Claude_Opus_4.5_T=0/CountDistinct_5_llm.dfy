
// Returns the number of distinct elements in a sorted array of integers.

ghost function CountDistinctSeq(s: seq<int>): nat
{
    if |s| == 0 then 0
    else if |s| == 1 then 1
    else if s[|s|-1] != s[|s|-2] then 1 + CountDistinctSeq(s[..|s|-1])
    else CountDistinctSeq(s[..|s|-1])
}

method CountDistinct(a: array<int>) returns (count: nat)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures count == CountDistinctSeq(a[..])
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
        invariant count == CountDistinctSeq(a[..i])
    {
        if a[i] != a[i-1] {
            count := count + 1;
        }
        else {
        }
    }
    return count;
}



method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert a[..] == [1, 1, 2, 2, 3];
    assert CountDistinctSeq([1, 1, 2, 2, 3]) == 3;
    assert count == 3;
}
