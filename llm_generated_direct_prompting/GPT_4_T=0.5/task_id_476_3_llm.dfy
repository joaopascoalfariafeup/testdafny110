// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == min(a[..]) + max(a[..])
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 0 <= i <= a.Length
    invariant minVal == min(a[..i])
    invariant maxVal == max(a[..i])
  {
    if a[i] < minVal {
      minVal := a[i];
    } 
    if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  sum := minVal + maxVal;
}

function min(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else min(s[..|s|-1]) < s[|s|-1] ? min(s[..|s|-1]) : s[|s|-1]
}

function max(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else max(s[..|s|-1]) > s[|s|-1] ? max(s[..|s|-1]) : s[|s|-1]
}

// Test cases checked statically.
method SumMinMaxTest(){
  var a1 := new int[] [1,2,3];
  var out1 := SumMinMax(a1);
  assert out1 == 4;

  var a2 := new int[] [-1,2,3,4];
  var out2 := SumMinMax(a2);
  assert out2 == 3;

  var a3 := new int[] [2,3,6];
  var out3 := SumMinMax(a3);
  assert out3 == 8;
}

