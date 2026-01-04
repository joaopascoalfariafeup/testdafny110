
// Returns the number of distinct elements in a sorted array of integers.

ghost predicate IsSorted(a: array<int>)
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

ghost function CountDistinctInSeq(s: seq<int>): nat
{
    if |s| == 0 then 0
    else if |s| == 1 then 1
    else if s[|s|-1] != s[|s|-2] then 1 + CountDistinctInSeq(s[..|s|-1])
    else CountDistinctInSeq(s[..|s|-1])
}

method CountDistinct(a: array<int>) returns (count: nat)
    requires IsSorted(a)
    ensures count == CountDistinctInSeq(a[..])
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
        invariant count == CountDistinctInSeq(a[..i])
    {
        if a[i] != a[i-1] {
            assert a[..i+1] == a[..i] + [a[i]];
            count := count + 1;
        }
        else {
            assert a[..i+1] == a[..i] + [a[i]];
        }
    }
    assert a[..a.Length] == a[..];
    return count;
}



method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    assert a[..] == [1, 1, 2, 2, 3];
    assert a[..1] == [1];
    assert a[..2] == [1, 1];
    assert a[..3] == [1, 1, 2];
    assert a[..4] == [1, 1, 2, 2];
    assert a[..5] == [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}
