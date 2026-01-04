// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == min(a[..]) + max(a[..])
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
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

// Helper functions for min and max of a sequence
function {:fuel 5} min(s: seq<int>): int
  requires |s| > 0
  ensures min(s) in s
  ensures forall i :: 0 <= i < |s| ==> s[i] >= min(s)
{
  if |s| == 1 then
    s[0]
  else
    var m := min(s[..|s|-1]);
    if s[|s|-1] < m then s[|s|-1] else m
}

function {:fuel 5} max(s: seq<int>): int
  requires |s| > 0
  ensures max(s) in s
  ensures forall i :: 0 <= i < |s| ==> s[i] <= max(s)
{
  if |s| == 1 then
    s[0]
  else
    var m := max(s[..|s|-1]);
    if s[|s|-1] > m then s[|s|-1] else m
}

// Test cases checked statically.
method SumMinMaxTest(){
  var a1 := new int[] [1,2,3];
  var out1 := SumMinMax(a1);
  assert a1[..] == [1,2,3];
  // Helper assertions to help Dafny compute min and max
  assert min([1,2,3]) == 1;
  assert max([1,2,3]) == 3;
  assert out1 == 4;

  var a2 := new int[] [-1,2,3,4];
  var out2 := SumMinMax(a2);
  assert a2[..] == [-1,2,3,4];
  // Helper assertions to help Dafny compute min and max
  assert min([-1,2,3,4]) == -1;
  assert max([-1,2,3,4]) == 4;
  assert out2 == 3;

  var a3 := new int[] [2,3,6];
  var out3 := SumMinMax(a3);
  assert a3[..] == [2,3,6];
  // Helper assertions to help Dafny compute min and max
  assert min([2,3,6]) == 2;
  assert max([2,3,6]) == 6;
  assert out3 == 8;
}

