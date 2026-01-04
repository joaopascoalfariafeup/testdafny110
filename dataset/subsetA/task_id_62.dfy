// Find the smallest number (minimum) in a non-empty array of integers.
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures isMin(s[..], min)
{
  min := s[0];
  for i := 1 to s.Length
    invariant isMin(s[..i], min)
  {
    if s[i] < min {
      min := s[i];
    }
  }
}

// Auxiliary (reusable) predicate to check the minimum of a sequence.
ghost predicate isMin(s: seq<int>, x: int) {
  (x in s) && (forall k :: 0 <= k < |s| ==> x <= s[k])
}

// Test cases checked statically
method FindSmallestTest(){
  // sorted array
  var a1 := new int[] [1, 2, 3];
  var out1 := FindSmallest(a1);
  assert a1[0] == 1; // proof helper (1 is in the array)
  assert out1 == 1;

  // unsorted array
  var a2 := new int[] [3, 2, 1, 4];
  var out2 := FindSmallest(a2);
  assert a2[2] == 1; // proof helper
  assert out2 == 1;

  // unsorted array with duplicate elements
  var a3 := new int[] [3, 3, 1, 4, 1];
  var out3 := FindSmallest(a3);
  assert a3[2] == a3[4] == 1; // proof helper
  assert out3 == 1;
}