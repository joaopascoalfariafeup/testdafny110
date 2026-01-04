
ghost function {:fuel 5} minSeq(s: seq<int>): int
  requires |s| > 0
  ensures minSeq(s) in s && forall k :: 0 <= k < |s| ==> s[k] >= minSeq(s)
{ if |s| == 1 then s[0] else if s[|s|-1] < minSeq(s[..|s|-1]) then s[|s|-1] else minSeq(s[..|s|-1])}

// Find the smallest number (minimum) in a non-empty array of integers.
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures min == minSeq(s[..]) && forall k :: 0 <= k < s.Length ==> min <= s[k]
{
  min := s[0];
  for i := 1 to s.Length
    invariant 0 <= i <= s.Length
    invariant min == minSeq(s[..i]) && forall k :: 0 <= k < i ==> min <= s[k]
  {
    if s[i] < min {
      min := s[i];
    }
  }
}

// Test cases checked statically
method FindSmallestTest(){
  // sorted array
  var a1 := new int[] [1, 2, 3];
  var out1 := FindSmallest(a1);
  assert out1 == 1;

  // unsorted array
  var a2 := new int[] [3, 2, 1, 4];
  var out2 := FindSmallest(a2);
  assert out2 == 1;

  // unsorted array with duplicate elements
  var a3 := new int[] [3, 3, 1, 4, 1];
  var out3 := FindSmallest(a3);
  assert out3 == 1;
}

