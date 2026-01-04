
ghost predicate HasAtLeastTwoDistinct(s: seq<int>)
{
  exists i, j :: 0 <= i < |s| && 0 <= j < |s| && s[i] != s[j]
}

ghost predicate IsMinIndex(s: seq<int>, mi: int)
{
  0 <= mi < |s| &&
  forall k :: 0 <= k < |s| ==> s[mi] <= s[k]
}

ghost predicate IsSecondMinIndex(s: seq<int>, mi: int, smi: int)
{
  0 <= mi < |s| &&
  0 <= smi < |s| &&
  s[mi] < s[smi] &&
  forall k :: 0 <= k < |s| && s[k] > s[mi] ==> s[smi] <= s[k]
}

// Obtains the smallest and second smallest element in an array of integers (in a single scan).
// The array must have at least two distinct elements.
method SecondSmallest(s: array<int>) returns (smallest: int, secondSmallest: int)
  requires s.Length >= 2
  requires HasAtLeastTwoDistinct(s[..])
  ensures smallest <= secondSmallest
  ensures smallest in s[..]
  ensures secondSmallest in s[..]
  ensures forall k :: 0 <= k < s.Length ==> smallest <= s[k]
  ensures forall k :: 0 <= k < s.Length && s[k] > smallest ==> secondSmallest <= s[k]
  ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && s[i] == smallest && s[j] == secondSmallest
{
    // index of the smallest element inspected so far.
    var minIndex := 0;

    // or -1 if all elements are equal so far.
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

    // At loop end, i == s.Length and secondMinIndex != -1 follows from HasAtLeastTwoDistinct
    // together with the invariant that secondMinIndex == -1 means all inspected elements are equal.
    assert secondMinIndex != -1;

    return s[minIndex], s[secondMinIndex];
}

// Test cases checked statically.
method SecondSmallestTest(){
    var a1:= new int[] [1, 2, -8, -2, -2, -8];
    assert a1[..] == [1, 2, -8, -2, -2, -8];
    // help witness HasAtLeastTwoDistinct
    assert a1[0] != a1[2];
    assert HasAtLeastTwoDistinct(a1[..]); // e.g., a1[0] != a1[2]
    var s1, out1 := SecondSmallest(a1);
    // help verifier connect postconditions to concrete values
    assert s1 in a1[..] && out1 in a1[..];
    assert forall k :: 0 <= k < a1.Length ==> s1 <= a1[k];
    assert forall k :: 0 <= k < a1.Length && a1[k] > s1 ==> out1 <= a1[k];
    assert s1 == -8 && out1 == -2;

    var a2:= new int[] [2, 2, 1];
    assert a2[..] == [2, 2, 1];
    assert a2[0] != a2[2];
    assert HasAtLeastTwoDistinct(a2[..]);
    var s2, out2 := SecondSmallest(a2);
    assert s2 in a2[..] && out2 in a2[..];
    assert forall k :: 0 <= k < a2.Length ==> s2 <= a2[k];
    assert forall k :: 0 <= k < a2.Length && a2[k] > s2 ==> out2 <= a2[k];
    assert s2 == 1 && out2 == 2;

    var a3:= new int[] [-2, -3, -1];
    assert a3[..] == [-2, -3, -1];
    assert a3[1] != a3[0];
    assert HasAtLeastTwoDistinct(a3[..]);
    var s3, out3 := SecondSmallest(a3);
    assert s3 in a3[..] && out3 in a3[..];
    assert forall k :: 0 <= k < a3.Length ==> s3 <= a3[k];
    assert forall k :: 0 <= k < a3.Length && a3[k] > s3 ==> out3 <= a3[k];
    assert s3 == -3 && out3 == -2;
}

