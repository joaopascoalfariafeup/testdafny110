// Finds the maximum difference between any two elements in a non-empty array.

function MinSeq(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then
    s[0]
  else
    (if s[|s|-1] < MinSeq(s[..|s|-1]) then s[|s|-1] else MinSeq(s[..|s|-1]))
}

function MaxSeq(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then
    s[0]
  else
    (if s[|s|-1] > MaxSeq(s[..|s|-1]) then s[|s|-1] else MaxSeq(s[..|s|-1]))
}

lemma MinSeqExtend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MinSeq(s + [x]) == (if x < MinSeq(s) then x else MinSeq(s))
  decreases |s|
{
  if |s| == 1 {
  } else {
    MinSeqExtend(s[..|s|-1], s[|s|-1]);
  }
}

lemma MaxSeqExtend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MaxSeq(s + [x]) == (if x > MaxSeq(s) then x else MaxSeq(s))
  decreases |s|
{
  if |s| == 1 {
  } else {
    MaxSeqExtend(s[..|s|-1], s[|s|-1]);
  }
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

    MinSeqExtend(a[..i], a[i]);
    MaxSeqExtend(a[..i], a[i]);
    assert minVal == MinSeq(a[..i+1]);
    assert maxVal == MaxSeq(a[..i+1]);
  }
  diff := maxVal - minVal;
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
