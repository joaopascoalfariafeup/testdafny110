// Returns the sum of the minimum and maximum elements of a non-empty array
ghost function Min(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else if s[|s|-1] < Min(s[..|s|-1]) then s[|s|-1]
  else Min(s[..|s|-1])
}

ghost function Max(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else if s[|s|-1] > Max(s[..|s|-1]) then s[|s|-1]
  else Max(s[..|s|-1])
}

method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == Min(a[..]) + Max(a[..])
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant minVal == Min(a[..i])
    invariant maxVal == Max(a[..i])
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





// Test cases checked statically.
method SumMinMaxTest(){
  var a1 := new int[] [1,2,3];
  var out1 := SumMinMax(a1);
  assert a1[..] == [1,2,3];
  assert Min([1,2,3]) == 1;
  assert Max([1,2,3]) == 3;
  assert out1 == 4;

  var a2 := new int[] [-1,2,3,4];
  var out2 := SumMinMax(a2);
  assert a2[..] == [-1,2,3,4];
  assert Min([-1,2,3,4]) == -1;
  assert Max([-1,2,3,4]) == 4;
  assert out2 == 3;

  var a3 := new int[] [2,3,6];
  var out3 := SumMinMax(a3);
  assert a3[..] == [2,3,6];
  assert Min([2,3,6]) == 2;
  assert Max([2,3,6]) == 6;
  assert out3 == 8;
}

