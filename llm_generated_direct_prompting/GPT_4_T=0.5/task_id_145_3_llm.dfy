// Auxiliary function to compute the minimum value in a sequence.
ghost function MinValue(s: seq<int>): int
  decreases |s|
{
  if |s| == 1 then s[0] else min(s[0], MinValue(s[1..]))
}

// Auxiliary function to compute the maximum value in a sequence.
ghost function MaxValue(s: seq<int>): int
  decreases |s|
{
  if |s| == 1 then s[0] else max(s[0], MaxValue(s[1..]))
}

// Finds the maximum difference between any two elements in a non-empty array.
method MaxDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0  // The array must not be empty.
  ensures diff == MaxValue(a[..]) - MinValue(a[..])  // The difference is the maximum value minus the minimum value.
{
  var minVal := a[0]; // minimum value in the array (so far)
  var maxVal := a[0]; // maximum value in the array (so far)
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal == MinValue(a[..i])
    invariant maxVal == MaxValue(a[..i])
  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }
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
