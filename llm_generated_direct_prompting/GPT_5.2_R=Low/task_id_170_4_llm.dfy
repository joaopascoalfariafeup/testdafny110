// Calculates the sum of elements in an array from a 'start' index
// (inclusive) to an 'end' index (exclusive).
// Itertative implementation.
function SumUpTo(s: seq<int>, n: nat): int
  requires n <= |s|
  decreases n
{
  if n == 0 then 0 else SumUpTo(s, n - 1) + s[n - 1]
}

function SumRange(s: seq<int>, start: nat, end: nat): int
  requires start <= end <= |s|
{
  SumUpTo(s, end) - SumUpTo(s, start)
}

method CalcSumRange(a: array<int>, start: nat := 0, end: nat := a.Length) returns (sum: int)
  requires start <= end <= a.Length
  ensures sum == SumRange(a[..], start, end)
{
  sum := 0;
  for i := start to end
    invariant start <= i <= end
    invariant end <= a.Length
    invariant sum == SumUpTo(a[..], i) - SumUpTo(a[..], start)
  {
    sum := sum + a[i];
    assert SumUpTo(a[..], i + 1) == SumUpTo(a[..], i) + a[i];
    assert sum == SumUpTo(a[..], i + 1) - SumUpTo(a[..], start);
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
