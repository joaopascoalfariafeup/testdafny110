// Finds the maximum difference between any two elements in a non-empty array.
method MaxDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && diff == a[j] - a[i]
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[j] - a[i] <= diff
{
  var minVal := a[0]; // minimum value in the array (so far)
  var maxVal := a[0]; // maximum value in the array (so far)
  for i := 1 to a.Length
    invariant exists k :: 0 <= k < i && minVal == a[k]
    invariant exists k :: 0 <= k < i && maxVal == a[k]
    invariant forall k :: 0 <= k < i ==> minVal <= a[k]
    invariant forall k :: 0 <= k < i ==> maxVal >= a[k]
  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  diff := maxVal - minVal;
}

// Helper lemma to prove uniqueness of max difference
lemma MaxDiffUnique(a: array<int>, diff: int)
  requires a.Length > 0
  requires exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && diff == a[j] - a[i]
  requires forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[j] - a[i] <= diff
{
  // Empty body - lemma just packages the preconditions
}

// Test cases checked statically.
method MaxDifferenceTest(){
  var a1:= new int[] [2, 1, 5, 3];
  assert a1[..] == [2, 1, 5, 3];
  assert a1[0] == 2 && a1[1] == 1 && a1[2] == 5 && a1[3] == 3;
  var out1 := MaxDifference(a1);
  // Help Dafny: min is 1 (at index 1), max is 5 (at index 2)
  assert a1[2] - a1[1] == 4;
  assert forall i, j :: 0 <= i < a1.Length && 0 <= j < a1.Length ==> a1[j] - a1[i] <= 4;
  assert out1 == 4 == 5 - 1;

  var a2:= new int[] [9,3,2,5,1];
  assert a2[..] == [9,3,2,5,1];
  assert a2[0] == 9 && a2[1] == 3 && a2[2] == 2 && a2[3] == 5 && a2[4] == 1;
  var out2 := MaxDifference(a2);
  // Help Dafny: min is 1 (at index 4), max is 9 (at index 0)
  assert a2[0] - a2[4] == 8;
  assert forall i, j :: 0 <= i < a2.Length && 0 <= j < a2.Length ==> a2[j] - a2[i] <= 8;
  assert out2 == 8 == 9 - 1;
  
  var a3:= new int[] [3,2,1];
  assert a3[..] == [3,2,1];
  assert a3[0] == 3 && a3[1] == 2 && a3[2] == 1;
  var out3 := MaxDifference(a3);
  // Help Dafny: min is 1 (at index 2), max is 3 (at index 0)
  assert a3[0] - a3[2] == 2;
  assert forall i, j :: 0 <= i < a3.Length && 0 <= j < a3.Length ==> a3[j] - a3[i] <= 2;
  assert out3 == 2 == 3 - 1;
}
