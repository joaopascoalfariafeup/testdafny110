// Calculates the sum of elements in an array from a 'start' index
// (inclusive) to an 'end' index (exclusive).
// Itertative implementation.
method CalcSumRange(a: array<int>, start: nat := 0, end: nat := a.Length) returns (sum: int)
  requires start <= end && end <= a.Length
  ensures sum == Sum(a[start..end])
{
  sum := 0;
  for i := start to end
    invariant sum == Sum(a[start..i+1])
    invariant start <= i <= end
  {
    sum := sum + a[i];
  }
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

// Auxiliary function for summing a sequence of integers
ghost function Sum(s: seq<int>): int
  requires |s| >= 0
  ensures Sum(s) >= 0
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..|s|])
}
