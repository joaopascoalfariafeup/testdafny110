// Find the smallest number (minimum) in a non-empty array of integers.
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures 0 <= min < s.Length
  ensures forall k :: 0 <= k < s.Length ==> s[k] >= s[min]
  ensures exists k :: 0 <= k < s.Length && s[k] == s[min]
{
  min := 0;
  for i := 1 to s.Length
    invariant 1 <= i <= s.Length
    invariant 0 <= min < s.Length
    invariant forall k :: 0 <= k < i ==> s[k] >= s[min]
    invariant exists k :: 0 <= k < i && s[k] == s[min]
  {
    if s[i] < s[min] {
      min := i;
    }
  }
}


// Test cases checked statically
method FindSmallestTest(){
  // sorted array
  var a1 := new int[] [1, 2, 3];
  var out1 := FindSmallest(a1);
  assert a1[out1] == 1;
  assert out1 == 0;

  // unsorted array
  var a2 := new int[] [3, 2, 1, 4];
  var out2 := FindSmallest(a2);
  assert a2[out2] == 1;
  assert out2 == 2;

  // unsorted array with duplicate elements
  var a3 := new int[] [3, 3, 1, 4, 1];
  var out3 := FindSmallest(a3);
  assert a3[out3] == 1;
  // The index could be 2 or 4, both contain 1
  assert out3 == 2 || out3 == 4;
}

