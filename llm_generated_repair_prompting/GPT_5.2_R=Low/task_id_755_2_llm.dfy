
predicate TwoDistinct(s: array<int>)
  reads s
{
  exists i, j :: 0 <= i < j < s.Length && s[i] != s[j]
}

lemma AllEqualNoDistinct(s: array<int>, v: int)
  requires forall k :: 0 <= k < s.Length ==> s[k] == v
  ensures !TwoDistinct(s)
{
  if TwoDistinct(s) {
    var i, j :| 0 <= i < j < s.Length && s[i] != s[j];
    assert s[i] == v;
    assert s[j] == v;
    assert false;
  }
}

// Obtains the smallest and second smallest element in an array of integers (in a single scan).
// The array must have at least two distinct elements.
method SecondSmallest(s: array<int>) returns (smallest: int, secondSmallest: int)
  requires s.Length >= 2
  requires TwoDistinct(s)
  ensures forall k :: 0 <= k < s.Length ==> smallest <= s[k]
  ensures exists k :: 0 <= k < s.Length && s[k] == smallest
  ensures smallest < secondSmallest
  ensures exists k :: 0 <= k < s.Length && s[k] == secondSmallest
  ensures forall k :: 0 <= k < s.Length ==> (s[k] > smallest ==> secondSmallest <= s[k])
{
    // index of the smallest element inspected so far.
    var minIndex := 0;

    // or -1 if all elements are equal so far.
    var secondMinIndex := -1;

    for i := 1 to s.Length
      invariant 1 <= i <= s.Length
      invariant 0 <= minIndex < i
      invariant -1 <= secondMinIndex < i
      invariant forall k :: 0 <= k < i ==> s[minIndex] <= s[k]
      invariant secondMinIndex == -1 ==> forall k :: 0 <= k < i ==> s[k] == s[minIndex]
      invariant secondMinIndex != -1 ==> s[minIndex] < s[secondMinIndex]
      invariant secondMinIndex != -1 ==> forall k :: 0 <= k < i ==> (s[k] > s[minIndex] ==> s[secondMinIndex] <= s[k])
    {
        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if s[i] > s[minIndex] && (secondMinIndex == -1 || s[i] < s[secondMinIndex]) {
            secondMinIndex := i;
        }
    }

    if secondMinIndex == -1 {
      assert forall k :: 0 <= k < s.Length ==> s[k] == s[minIndex];
      AllEqualNoDistinct(s, s[minIndex]);
      assert false;
    }

    return s[minIndex], s[secondMinIndex];
}

// Test cases checked statically.
method SecondSmallestTest(){
    var a1:= new int[] [1, 2, -8, -2, -2, -8];
    assert a1.Length == 6;
    assert a1[0] == 1 && a1[1] == 2 && a1[2] == -8 && a1[3] == -2 && a1[4] == -2 && a1[5] == -8;

    assert 0 <= 0 < 2 < a1.Length;
    assert a1[0] != a1[2];
    assert TwoDistinct(a1);

    var s1, out1 := SecondSmallest(a1);

    // Prove s1 == -8
    assert s1 <= a1[2];
    assert s1 <= -8;
    var k1 :| 0 <= k1 < a1.Length && a1[k1] == s1;
    assert a1[0] >= -8 && a1[1] >= -8 && a1[2] >= -8 && a1[3] >= -8 && a1[4] >= -8 && a1[5] >= -8;
    assert a1[k1] >= -8;
    assert s1 >= -8;
    assert s1 == -8;

    // Prove out1 == -2
    assert a1[3] > s1;
    assert out1 <= a1[3];
    assert out1 <= -2;
    var k2 :| 0 <= k2 < a1.Length && a1[k2] == out1;
    assert out1 > s1;
    assert out1 > -8;
    // all elements > -8 are >= -2 in this array
    assert a1[0] > -8 ==> a1[0] >= -2;
    assert a1[1] > -8 ==> a1[1] >= -2;
    assert a1[2] > -8 ==> a1[2] >= -2;
    assert a1[3] > -8 ==> a1[3] >= -2;
    assert a1[4] > -8 ==> a1[4] >= -2;
    assert a1[5] > -8 ==> a1[5] >= -2;
    assert a1[k2] > -8 ==> a1[k2] >= -2;
    assert a1[k2] > -8;
    assert out1 >= -2;
    assert out1 == -2;

    assert  s1 == -8 && out1 == -2;

    var a2:= new int[] [2, 2, 1];
    assert a2.Length == 3;
    assert a2[0] == 2 && a2[1] == 2 && a2[2] == 1;
    assert a2[0] != a2[2];
    assert TwoDistinct(a2);

    var s2, out2 := SecondSmallest(a2);
    assert s2 == 1 && out2 == 2;

    var a3:= new int[] [-2, -3, -1];
    assert a3.Length == 3;
    assert a3[0] == -2 && a3[1] == -3 && a3[2] == -1;
    assert a3[1] != a3[0];
    assert TwoDistinct(a3);

    var s3, out3 := SecondSmallest(a3);
    assert s3 == -3 && out3 == -2;
}

