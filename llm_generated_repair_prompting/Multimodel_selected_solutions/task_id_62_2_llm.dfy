// Find the smallest number (minimum) in a non-empty array of integers.
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall k :: 0 <= k < s.Length ==> min <= s[k]
  ensures exists k :: 0 <= k < s.Length && min == s[k]
{
  min := s[0];
  for i := 1 to s.Length
    invariant forall k :: 0 <= k < i ==> min <= s[k]
    invariant exists k :: 0 <= k < i && min == s[k]
  {
    if s[i] < min {
      min := s[i];
    }
  }
}

// Helper lemma to prove uniqueness of minimum
lemma MinIsUnique(s: array<int>, min1: int, min2: int)
  requires s.Length > 0
  requires forall k :: 0 <= k < s.Length ==> min1 <= s[k]
  requires exists k :: 0 <= k < s.Length && min1 == s[k]
  requires forall k :: 0 <= k < s.Length ==> min2 <= s[k]
  requires exists k :: 0 <= k < s.Length && min2 == s[k]
  ensures min1 == min2
{
  var i :| 0 <= i < s.Length && min1 == s[i];
  var j :| 0 <= j < s.Length && min2 == s[j];
  assert min1 <= s[j] == min2;
  assert min2 <= s[i] == min1;
}

// Test cases checked statically
method FindSmallestTest(){
  // sorted array
  var a1 := new int[] [1, 2, 3];
  assert a1[0] == 1 && a1[1] == 2 && a1[2] == 3;
  var out1 := FindSmallest(a1);
  // Prove that 1 satisfies the postconditions
  assert a1[0] == 1;
  assert forall k :: 0 <= k < a1.Length ==> 1 <= a1[k];
  MinIsUnique(a1, out1, 1);
  assert out1 == 1;

  // unsorted array
  var a2 := new int[] [3, 2, 1, 4];
  assert a2[0] == 3 && a2[1] == 2 && a2[2] == 1 && a2[3] == 4;
  var out2 := FindSmallest(a2);
  // Prove that 1 satisfies the postconditions
  assert a2[2] == 1;
  assert forall k :: 0 <= k < a2.Length ==> 1 <= a2[k];
  MinIsUnique(a2, out2, 1);
  assert out2 == 1;

  // unsorted array with duplicate elements
  var a3 := new int[] [3, 3, 1, 4, 1];
  assert a3[0] == 3 && a3[1] == 3 && a3[2] == 1 && a3[3] == 4 && a3[4] == 1;
  var out3 := FindSmallest(a3);
  // Prove that 1 satisfies the postconditions
  assert a3[2] == 1;
  assert forall k :: 0 <= k < a3.Length ==> 1 <= a3[k];
  MinIsUnique(a3, out3, 1);
  assert out3 == 1;
}
