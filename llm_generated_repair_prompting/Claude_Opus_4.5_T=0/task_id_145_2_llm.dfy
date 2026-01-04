// Helper function to find minimum value in a sequence
ghost function seqMin(s: seq<int>): int
  requires |s| > 0
  ensures seqMin(s) in s
  ensures forall k :: 0 <= k < |s| ==> seqMin(s) <= s[k]
{
  if |s| == 1 then s[0]
  else if s[|s|-1] < seqMin(s[..|s|-1]) then s[|s|-1]
  else seqMin(s[..|s|-1])
}

// Helper function to find maximum value in a sequence
ghost function seqMax(s: seq<int>): int
  requires |s| > 0
  ensures seqMax(s) in s
  ensures forall k :: 0 <= k < |s| ==> seqMax(s) >= s[k]
{
  if |s| == 1 then s[0]
  else if s[|s|-1] > seqMax(s[..|s|-1]) then s[|s|-1]
  else seqMax(s[..|s|-1])
}

// Finds the maximum difference between any two elements in a non-empty array.
method MaxDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && diff == a[j] - a[i]
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[j] - a[i] <= diff
  ensures diff == seqMax(a[..]) - seqMin(a[..])
{
  var minVal := a[0]; // minimum value in the array (so far)
  var maxVal := a[0]; // maximum value in the array (so far)
  for i := 1 to a.Length
    invariant exists k :: 0 <= k < i && minVal == a[k]
    invariant exists k :: 0 <= k < i && maxVal == a[k]
    invariant forall k :: 0 <= k < i ==> minVal <= a[k]
    invariant forall k :: 0 <= k < i ==> maxVal >= a[k]
    invariant minVal == seqMin(a[..i])
    invariant maxVal == seqMax(a[..i])
  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  assert a[..a.Length] == a[..];
  diff := maxVal - minVal;
}

// Test cases checked statically.
method MaxDifferenceTest(){
  var a1:= new int[] [2, 1, 5, 3];
  assert a1[..] == [2, 1, 5, 3];
  var out1 := MaxDifference(a1);
  assert seqMin(a1[..]) == 1;
  assert seqMax(a1[..]) == 5;
  assert out1 == 4 == 5 - 1;

  var a2:= new int[] [9,3,2,5,1];
  assert a2[..] == [9,3,2,5,1];
  var out2 := MaxDifference(a2);
  assert seqMin(a2[..]) == 1;
  assert seqMax(a2[..]) == 9;
  assert out2 == 8 == 9 - 1;
  
  var a3:= new int[] [3,2,1];
  assert a3[..] == [3,2,1];
  var out3 := MaxDifference(a3);
  assert seqMin(a3[..]) == 1;
  assert seqMax(a3[..]) == 3;
  assert out3 == 2 == 3 - 1;
}
