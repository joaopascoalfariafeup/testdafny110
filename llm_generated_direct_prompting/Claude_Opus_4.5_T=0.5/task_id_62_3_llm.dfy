// Find the smallest number (minimum) in a non-empty array of integers.

ghost function Min(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else if s[|s|-1] < Min(s[..|s|-1]) then s[|s|-1]
  else Min(s[..|s|-1])
}

ghost predicate IsMinimum(m: int, s: seq<int>)
{
  (exists k :: 0 <= k < |s| && s[k] == m) &&
  (forall k :: 0 <= k < |s| ==> m <= s[k])
}

lemma MinIsMinimum(s: seq<int>)
  requires |s| > 0
  ensures IsMinimum(Min(s), s)
{
  if |s| == 1 {
  } else {
    MinIsMinimum(s[..|s|-1]);
  }
}

method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures IsMinimum(min, s[..])
{
  min := s[0];
  for i := 1 to s.Length
    invariant IsMinimum(min, s[..i])
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
