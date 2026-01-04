// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == Min(a[..]) + Max(a[..])
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 0 <= i <= a.Length
    invariant minVal == Min(a[..i]) && maxVal == Max(a[..i])
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

// Auxiliary function to get the minimum value in a sequence
function {:fuel 5} Min(s: seq<int>): int
  requires |s| > 0
  ensures Min(s) in s && forall k :: 0 <= k < |s| ==> s[k] >= Min(s)
{
  if |s| == 1 then s[0] else if s[0] < Min(s[1..]) then s[0] else Min(s[1..])
}

// Auxiliary function to get the maximum value in a sequence
function {:fuel 5} Max(s: seq<int>): int
  requires |s| > 0
  ensures Max(s) in s && forall k :: 0 <= k < |s| ==> s[k] <= Max(s)
{
  if |s| == 1 then s[0] else if s[0] > Max(s[1..]) then s[0] else Max(s[1..])
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
