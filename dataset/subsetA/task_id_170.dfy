// Calculates the sum of elements in an array from a 'start' index
// (inclusive) to an 'end' index (exclusive).
// Itertative implementation.
method CalcSumRange(a: array<int>, start: nat := 0, end: nat := a.Length) returns (sum: int)
  requires 0 <= start <= end <= a.Length
  ensures sum == SumSeq(a[start..end]) 
{
  sum := 0;
  for i := start to end
    invariant sum == SumSeq(a[start..i])
  {
    sum := sum + a[i];
    assert a[start..i+1] == a[start..i] + [a[i]]; // proof helper

  }
}

// Recursive definition of the sum of elements in a sequence.
ghost function {:fuel 4} SumSeq(s: seq<int>): int {
  if |s| == 0 then 0 else s[|s|-1] + SumSeq(s[..|s|-1])
}

// Test cases checked statically.
method SumInRangeTest(){
  var a1 := new int[] [2, 1, 5, 6];
  var s0 := CalcSumRange(a1, 0, 0);
  assert s0 == 0;
  var s1 := CalcSumRange(a1, 1, 2);
  assert s1 == 1;
  var s2 := CalcSumRange(a1, 1, 3);
  assert s2 == 6;
  var s3 := CalcSumRange(a1, 0, 2);
  assert s3 == 3;
  var s5 := CalcSumRange(a1, 0, 4);
  assert s5 == 14;
}