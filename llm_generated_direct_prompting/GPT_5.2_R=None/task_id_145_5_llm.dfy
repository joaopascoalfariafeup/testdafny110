// Finds the maximum difference between any two elements in a non-empty array.
method MaxDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  ensures diff == (var mx := (if exists k :: 0 <= k < a.Length then a[k] else 0);
                   var mn := (if exists k :: 0 <= k < a.Length then a[k] else 0);
                   (assert exists k :: 0 <= k < a.Length;
                    mx - mn))
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && diff == a[i] - a[j]
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
{
  var minVal := a[0]; // minimum value in the array (so far)
  var maxVal := a[0]; // maximum value in the array (so far)
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant exists k :: 0 <= k < i && minVal == a[k]
    invariant exists k :: 0 <= k < i && maxVal == a[k]
    invariant forall k :: 0 <= k < i ==> minVal <= a[k]
    invariant forall k :: 0 <= k < i ==> a[k] <= maxVal
  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  diff := maxVal - minVal;

  assert forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff;
  assert exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && diff == a[i] - a[j];
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
