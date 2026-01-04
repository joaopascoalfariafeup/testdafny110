// Calculates the sum of elements in an array from a 'start' index
// (inclusive) to an 'end' index (exclusive).
// Itertative implementation.
method CalcSumRange(a: array<int>, start: nat := 0, end: nat := a.Length) returns (sum: int)
  requires start <= end <= a.Length
  ensures sum == SumSeq(a[start..end])
{
  ghost var seqA := a[..];
  sum := 0;
  for i := start to end
    invariant start <= i <= end
    invariant sum == SumSeq(seqA[start..i])
  {
    sum := sum + a[i];
    // Helper assertion to maintain the invariant
    assert seqA[start..i+1] == seqA[start..i] + [seqA[i]];
  }
}

ghost function {:fuel 4} SumSeq(s: seq<int>): int
  decreases |s|
  ensures |s| == 0 ==> SumSeq(s) == 0
  ensures |s| > 0 ==> SumSeq(s) == s[|s|-1] + SumSeq(s[..|s|-1])
{
  if |s| == 0 then 0 else s[|s|-1] + SumSeq(s[..|s|-1])
}

// Test cases checked statically.
method SumInRangeTest(){
  var a1 := new int[] [2, 1, 5, 6];
  // Helper assertions to establish array content
  assert a1[..] == [2, 1, 5, 6];
  var s0 := CalcSumRange(a1, 0, 0);
  assert s0 == 0;
  var s1 := CalcSumRange(a1, 1, 2);
  assert s1 == 1;
  var s2 := CalcSumRange(a1, 1, 3);
  assert s2 == 6;
  var s3 := CalcSumRange(a1, 0, 2);
  assert s3 == 3;
  var s5 := CalcSumRange(a1, 0, 4);
  // Helper calculation for the full sum
  calc {
    SumSeq([2, 1, 5, 6]);
    == { assert [2, 1, 5, 6][3] == 6; }
    6 + SumSeq([2, 1, 5]);
    == { assert [2, 1, 5][2] == 5; }
    6 + 5 + SumSeq([2, 1]);
    == { assert [2, 1][1] == 1; }
    6 + 5 + 1 + SumSeq([2]);
    == { assert [2][0] == 2; }
    6 + 5 + 1 + 2 + SumSeq([]);
    ==
    6 + 5 + 1 + 2 + 0;
    ==
    14;
  }
  assert SumSeq([2, 1, 5, 6]) == 14;
  assert s5 == 14;
}


