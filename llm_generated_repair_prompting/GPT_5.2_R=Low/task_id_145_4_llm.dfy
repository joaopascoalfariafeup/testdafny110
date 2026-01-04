function {:fuel 10} MinSeq(s: seq<int>): int
  requires |s| > 0
  ensures MinSeq(s) in s
  ensures forall k :: 0 <= k < |s| ==> MinSeq(s) <= s[k]
{
  if |s| == 1 then s[0]
  else
    (if s[|s|-1] < MinSeq(s[..|s|-1]) then s[|s|-1] else MinSeq(s[..|s|-1]))
}

function {:fuel 10} MaxSeq(s: seq<int>): int
  requires |s| > 0
  ensures MaxSeq(s) in s
  ensures forall k :: 0 <= k < |s| ==> s[k] <= MaxSeq(s)
{
  if |s| == 1 then s[0]
  else
    (if s[|s|-1] > MaxSeq(s[..|s|-1]) then s[|s|-1] else MaxSeq(s[..|s|-1]))
}

lemma MinSeqAppend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MinSeq(s + [x]) == (if x < MinSeq(s) then x else MinSeq(s))
{
  if |s| == 1 {
  } else {
    MinSeqAppend(s[..|s|-1], s[|s|-1]);
  }
}

lemma MaxSeqAppend(s: seq<int>, x: int)
  requires |s| > 0
  ensures MaxSeq(s + [x]) == (if x > MaxSeq(s) then x else MaxSeq(s))
{
  if |s| == 1 {
  } else {
    MaxSeqAppend(s[..|s|-1], s[|s|-1]);
  }
}

// Helper lemma to make the second test provable: compute MinSeq/MaxSeq for that concrete sequence
lemma MinMax_93251(s: seq<int>)
  requires s == [9,3,2,5,1]
  ensures MinSeq(s) == 1
  ensures MaxSeq(s) == 9
{
  // Establish simple bounds for all elements of s
  forall k | 0 <= k < |s|
    ensures s[k] >= 1
  {
    if k == 0 { }
    else if k == 1 { }
    else if k == 2 { }
    else if k == 3 { }
    else { } // k==4
  }

  forall k | 0 <= k < |s|
    ensures s[k] <= 9
  {
    if k == 0 { }
    else if k == 1 { }
    else if k == 2 { }
    else if k == 3 { }
    else { } // k==4
  }

  // MinSeq(s) >= 1 because MinSeq(s) is an element of s and all elements are >= 1
  assert MinSeq(s) in s;
  assert forall k :: 0 <= k < |s| ==> s[k] >= 1;
  // use the "in s" fact to get a witness index
  var i :| 0 <= i < |s| && s[i] == MinSeq(s);
  assert MinSeq(s) >= 1;

  // MinSeq(s) <= 1 because s[4]=1 and MinSeq(s) <= every element
  assert s[4] == 1;
  assert forall k :: 0 <= k < |s| ==> MinSeq(s) <= s[k];
  assert MinSeq(s) <= s[4];
  assert MinSeq(s) <= 1;

  assert MinSeq(s) == 1;

  // MaxSeq(s) <= 9 because MaxSeq(s) is an element of s and all elements are <= 9
  assert MaxSeq(s) in s;
  assert forall k :: 0 <= k < |s| ==> s[k] <= 9;
  var j :| 0 <= j < |s| && s[j] == MaxSeq(s);
  assert MaxSeq(s) <= 9;

  // MaxSeq(s) >= 9 because s[0]=9 and every element is <= MaxSeq(s)
  assert s[0] == 9;
  assert forall k :: 0 <= k < |s| ==> s[k] <= MaxSeq(s);
  assert s[0] <= MaxSeq(s);
  assert 9 <= MaxSeq(s);

  assert MaxSeq(s) == 9;
}

// Finds the maximum difference between any two elements in a non-empty array.
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
    var oldMin := minVal;
    var oldMax := maxVal;

    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }

    // Connect the updates to a conditional-expression form
    assert minVal == (if a[i] < oldMin then a[i] else oldMin);
    assert maxVal == (if a[i] > oldMax then a[i] else oldMax);

    assert a[..i+1] == a[..i] + [a[i]];

    // Rewrite oldMin/oldMax using the loop invariants
    assert oldMin == MinSeq(a[..i]);
    assert oldMax == MaxSeq(a[..i]);

    MinSeqAppend(a[..i], a[i]);
    MaxSeqAppend(a[..i], a[i]);

    assert minVal == MinSeq(a[..i+1]);
    assert maxVal == MaxSeq(a[..i+1]);
  }
  // At loop exit, i == a.Length, so the invariants give min/max over the whole array
  assert minVal == MinSeq(a[..]);
  assert maxVal == MaxSeq(a[..]);
  diff := maxVal - minVal;
}

// Test cases checked statically.
method MaxDifferenceTest(){
  var a1:= new int[] [2, 1, 5, 3];
  assert a1[..] == [2, 1, 5, 3];
  var out1 := MaxDifference(a1);
  assert out1 == 4 == 5 - 1;

  var a2:= new int[] [9,3,2,5,1];
  assert a2[..] == [9, 3, 2, 5, 1];
  MinMax_93251(a2[..]);
  var out2 := MaxDifference(a2);
  assert out2 == 8 == 9 - 1;
  
  var a3:= new int[] [3,2,1];
  assert a3[..] == [3, 2, 1];
  var out3 := MaxDifference(a3);
  assert out3 == 2 == 3 - 1;
}
