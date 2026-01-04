
// Obtains the smallest and second smallest element in an array of integers (in a single scan).
// The array must have at least two distinct elements.

ghost predicate HasTwoDistinct(s: array<int>)
    reads s
{
    exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && s[i] != s[j]
}

ghost predicate IsMinInRange(s: array<int>, idx: int, lo: int, hi: int)
    reads s
    requires 0 <= lo <= hi <= s.Length
{
    lo <= idx < hi && forall k :: lo <= k < hi ==> s[idx] <= s[k]
}

ghost predicate IsSecondMinInRange(s: array<int>, minIdx: int, secondMinIdx: int, lo: int, hi: int)
    reads s
    requires 0 <= lo <= hi <= s.Length
    requires 0 <= minIdx < s.Length
{
    lo <= secondMinIdx < hi && 
    s[minIdx] < s[secondMinIdx] &&
    forall k :: lo <= k < hi && s[k] > s[minIdx] ==> s[secondMinIdx] <= s[k]
}

ghost predicate AllEqualInRange(s: array<int>, lo: int, hi: int)
    reads s
    requires 0 <= lo <= hi <= s.Length
{
    forall i, j :: lo <= i < hi && lo <= j < hi ==> s[i] == s[j]
}

method SecondSmallest(s: array<int>) returns (smallest: int, secondSmallest: int)
    requires HasTwoDistinct(s)
    ensures exists i :: 0 <= i < s.Length && smallest == s[i] && forall k :: 0 <= k < s.Length ==> smallest <= s[k]
    ensures exists j :: 0 <= j < s.Length && secondSmallest == s[j] && smallest < secondSmallest && forall k :: 0 <= k < s.Length && s[k] > smallest ==> secondSmallest <= s[k]
{
    // index of the smallest element inspected so far.
    var minIndex := 0; 

    // or -1 if all elements are equal so far.
    var secondMinIndex := -1; 

    for i := 1 to s.Length
        invariant IsMinInRange(s, minIndex, 0, i)
        invariant secondMinIndex == -1 ==> AllEqualInRange(s, 0, i)
        invariant secondMinIndex != -1 ==> IsSecondMinInRange(s, minIndex, secondMinIndex, 0, i)
    {
        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if s[i] > s[minIndex] && (secondMinIndex == -1 || s[i] < s[secondMinIndex]) {
            secondMinIndex := i;
        }
    }


    return s[minIndex], s[secondMinIndex];
}

// Test cases checked statically.
method SecondSmallestTest(){
    var a1:= new int[] [1, 2, -8, -2, -2, -8];
    assert a1[0] != a1[2];
    var s1, out1 := SecondSmallest(a1);
    assert out1 <= a1[3] && a1[3] <= out1;
    assert  s1 == -8 && out1 == -2;

    var a2:= new int[] [2, 2, 1];
    assert a2[0] != a2[2];
    var s2, out2 := SecondSmallest(a2);
    assert s2 == 1 && out2 == 2;

    var a3:= new int[] [-2, -3, -1];
    assert a3[1] != a3[0];
    var s3, out3 := SecondSmallest(a3);
    assert s3 == -3 && out3 == -2;
}