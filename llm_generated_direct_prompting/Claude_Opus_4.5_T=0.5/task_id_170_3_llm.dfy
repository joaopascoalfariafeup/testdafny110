// Calculates the sum of elements in an array from a 'start' index
// (inclusive) to an 'end' index (exclusive).
// Itertative implementation.

ghost function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0 else s[|s|-1] + SumSeq(s[..|s|-1])
}

method CalcSumRange(a: array<int>, start: nat := 0, end: nat := a.Length) returns (sum: int)
  requires start <= end <= a.Length
  ensures sum == SumSeq(a[start..end])
{
  sum := 0;
  for i := start to end
    invariant start <= i <= end
    invariant sum == SumSeq(a[start..i])
  {
    sum := sum + a[i];

  }
}


// Test cases checked statically.
method SumInRangeTest(){
  var a1 := new int[] [2, 1, 5, 6];
  var s0 := CalcSumRange(a1, 0, 0);
  assert a1[0..0] == [];
  assert s0 == 0;
  var s1 := CalcSumRange(a1, 1, 2);
  assert a1[1..2] == [1];
  assert SumSeq([1]) == 1 + SumSeq([]);
  assert s1 == 1;
  var s2 := CalcSumRange(a1, 1, 3);
  assert a1[1..3] == [1, 5];
  assert SumSeq([1, 5]) == 5 + SumSeq([1]);
  assert s2 == 6;
  var s3 := CalcSumRange(a1, 0, 2);
  assert a1[0..2] == [2, 1];
  assert SumSeq([2, 1]) == 1 + SumSeq([2]);
  assert s3 == 3;
  var s5 := CalcSumRange(a1, 0, 4);
  assert a1[0..4] == [2, 1, 5, 6];
  assert SumSeq([2, 1, 5, 6]) == 6 + SumSeq([2, 1, 5]);
  assert SumSeq([2, 1, 5]) == 5 + SumSeq([2, 1]);
  assert SumSeq([2, 1]) == 1 + SumSeq([2]);
  assert SumSeq([2]) == 2 + SumSeq([]);
  assert s5 == 14;
}
