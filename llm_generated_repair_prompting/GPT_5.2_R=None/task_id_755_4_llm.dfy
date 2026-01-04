
ghost predicate HasAtLeastTwoDistinct(s: seq<int>)
{
  exists i, j :: 0 <= i < |s| && 0 <= j < |s| && s[i] != s[j]
}

method SecondSmallest(s: array<int>) returns (smallest: int, secondSmallest: int)
  requires s.Length >= 2
  requires HasAtLeastTwoDistinct(s[..])
  ensures smallest <= secondSmallest
  ensures smallest in s[..]
  ensures secondSmallest in s[..]
  ensures forall k :: 0 <= k < s.Length ==> smallest <= s[k]
  ensures forall k :: 0 <= k < s.Length && s[k] > smallest ==> secondSmallest <= s[k]
  // Strengthen: secondSmallest is strictly greater than smallest (possible because of distinctness)
  ensures smallest < secondSmallest
{
    var minIndex := 0;
    var secondMinIndex := -1;

    for i := 1 to s.Length
      invariant 1 <= i <= s.Length
      invariant 0 <= minIndex < i
      invariant -1 <= secondMinIndex < i
      invariant secondMinIndex == -1 || s[minIndex] < s[secondMinIndex]
      invariant forall k :: 0 <= k < i ==> s[minIndex] <= s[k]
      invariant secondMinIndex == -1 ==> forall k :: 0 <= k < i ==> s[k] == s[minIndex]
      invariant secondMinIndex != -1 ==> forall k :: 0 <= k < i && s[k] > s[minIndex] ==> s[secondMinIndex] <= s[k]
    {
        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if s[i] > s[minIndex] && (secondMinIndex == -1 || s[i] < s[secondMinIndex]) {
            secondMinIndex := i;
        }
    }

    // Prove secondMinIndex != -1 from HasAtLeastTwoDistinct and the invariant meaning of -1
    if secondMinIndex == -1 {
      assert forall k :: 0 <= k < s.Length ==> s[k] == s[minIndex];
      assert !HasAtLeastTwoDistinct(s[..]);
      assert false;
    }
    assert secondMinIndex != -1;

    return s[minIndex], s[secondMinIndex];
}

method SecondSmallestTest(){
    var a1:= new int[] [1, 2, -8, -2, -2, -8];
    assert a1[..] == [1, 2, -8, -2, -2, -8];
    assert a1[0] != a1[2];
    assert HasAtLeastTwoDistinct(a1[..]);
    var s1, out1 := SecondSmallest(a1);

    // Help Dafny derive the unique concrete values from the min/2nd-min properties + membership
    assert s1 == -8;
    assert out1 == -2;
    assert s1 == -8 && out1 == -2;

    var a2:= new int[] [2, 2, 1];
    assert a2[..] == [2, 2, 1];
    assert a2[0] != a2[2];
    assert HasAtLeastTwoDistinct(a2[..]);
    var s2, out2 := SecondSmallest(a2);

    assert s2 == 1;
    assert out2 == 2;
    assert s2 == 1 && out2 == 2;

    var a3:= new int[] [-2, -3, -1];
    assert a3[..] == [-2, -3, -1];
    assert a3[1] != a3[0];
    assert HasAtLeastTwoDistinct(a3[..]);
    var s3, out3 := SecondSmallest(a3);

    assert s3 == -3;
    assert out3 == -2;
    assert s3 == -3 && out3 == -2;
}

