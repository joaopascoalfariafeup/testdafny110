// A ghost function that returns the minimum element of a non-empty sequence
ghost function {:fuel 10} MinSeq(s: seq<int>): int
  requires |s| > 0
  ensures MinSeq(s) in s
  ensures forall k :: 0 <= k < |s| ==> MinSeq(s) <= s[k]
{
  if |s| == 1 then
    s[0]
  else
    if s[|s|-1] < MinSeq(s[..|s|-1]) then s[|s|-1] else MinSeq(s[..|s|-1])
}

// Useful unfolding for the “extend by one element at the end” pattern
lemma MinSeqExtend(a: array<int>, i: int)
  requires a != null
  requires 1 <= i < a.Length
  ensures MinSeq(a[..i+1]) == (if a[i] < MinSeq(a[..i]) then a[i] else MinSeq(a[..i]))
{
  // By unfolding MinSeq on the sequence a[..i+1], whose last element is a[i]
}

// Find the smallest number (minimum) in a non-empty array of integers.
method FindSmallest(s: array<int>) returns (min: int)
  requires s != null
  requires s.Length > 0
  ensures min == MinSeq(s[..])
  ensures forall k :: 0 <= k < s.Length ==> min <= s[k]
  ensures exists k :: 0 <= k < s.Length && s[k] == min
{
  min := s[0];
  for i := 1 to s.Length
    invariant 1 <= i <= s.Length
    invariant min == MinSeq(s[..i])
  {
    if s[i] < min {
      min := s[i];
    }
    // Help Dafny re-establish the invariant after i is incremented
    if i < s.Length {
      MinSeqExtend(s, i);
    }
    assert min == MinSeq(s[..i+1]);
  }
}


// Test cases checked statically
method FindSmallestTest(){
  // sorted array
  var a1 := new int[] [1, 2, 3];
  assert a1[..] == [1,2,3];
  var out1 := FindSmallest(a1);
  assert out1 == 1;

  // unsorted array
  var a2 := new int[] [3, 2, 1, 4];
  assert a2[..] == [3,2,1,4];
  var out2 := FindSmallest(a2);
  assert out2 == 1;

  // unsorted array with duplicate elements
  var a3 := new int[] [3, 3, 1, 4, 1];
  assert a3[..] == [3,3,1,4,1];
  var out3 := FindSmallest(a3);
  assert out3 == 1;
}
