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


// Test cases checked statically.
method MaxDifferenceTest(){
  var a1:= new int[] [2, 1, 5, 3];
  assert a1[0] == 2 && a1[1] == 1 && a1[2] == 5 && a1[3] == 3;
  var out1 := MaxDifference(a1);
  assert out1 == 4 == 5 - 1;

  var a2:= new int[] [9,3,2,5,1];
  assert a2[0] == 9 && a2[1] == 3 && a2[2] == 2 && a2[3] == 5 && a2[4] == 1;
  var out2 := MaxDifference(a2);
  assert out2 == 8 == 9 - 1;
  
  var a3:= new int[] [3,2,1];
  assert a3[0] == 3 && a3[1] == 2 && a3[2] == 1;
  var out3 := MaxDifference(a3);
  assert out3 == 2 == 3 - 1;
}