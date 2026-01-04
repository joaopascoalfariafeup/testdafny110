// Finds the maximum difference between any two elements in a non-empty array.
function {:fuel 10} MinSeq(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else
    var m := MinSeq(s[..|s|-1]);
    if s[|s|-1] < m then s[|s|-1] else m
}

function {:fuel 10} MaxSeq(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else
    var m := MaxSeq(s[..|s|-1]);
    if s[|s|-1] > m then s[|s|-1] else m
}

method MaxDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  ensures diff == MaxSeq(a[..]) - MinSeq(a[..])
{
  var minVal := a[0]; // minimum value in the array (so far)
  var maxVal := a[0]; // maximum value in the array (so far)
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal == MinSeq(a[..i])
    invariant maxVal == MaxSeq(a[..i])
  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }
    assert a[..i+1] == a[..i] + [a[i]];
    assert minVal == MinSeq(a[..i+1]);
    assert maxVal == MaxSeq(a[..i+1]);
  }
  diff := maxVal - minVal;
  assert diff == MaxSeq(a[..]) - MinSeq(a[..]);
}

// Test cases checked statically.
method MaxDifferenceTest(){
  var a1:= new int[] [2, 1, 5, 3];
  var out1 := MaxDifference(a1);
  assert out1 == 4 == 5 - 1;

  var a2:= new int[] [9,3,2,5,1];
  var out2 := MaxDifference(a2);
  assert out2 == 8 == 9 - 1;
  
  var a3:= new int[] [3,2,1];
  var out3 := MaxDifference(a3);
  assert out3 == 2 == 3 - 1;
}
