// Finds the maximum difference between any two elements in a non-empty array.
method MaxDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  ensures diff >= 0
  ensures (exists i :: 0 <= i < a.Length && (forall k :: 0 <= k < a.Length ==> a[i] <= a[k]))
  ensures (exists j :: 0 <= j < a.Length && (forall k :: 0 <= k < a.Length ==> a[j] >= a[k]))
  ensures diff ==
    (var min := (if (exists i :: 0 <= i < a.Length && (forall k :: 0 <= k < a.Length ==> a[i] <= a[k])) then a[0] else a[0]);
     var max := (if (exists j :: 0 <= j < a.Length && (forall k :: 0 <= k < a.Length ==> a[j] >= a[k])) then a[0] else a[0]);
     (max - min))
  ensures forall j, k :: 0 <= j < a.Length && 0 <= k < a.Length ==> a[j] - a[k] <= diff
  ensures exists j, k :: 0 <= j < a.Length && 0 <= k < a.Length && a[j] - a[k] == diff
{
  var minVal := a[0]; // minimum value in the array (so far)
  var maxVal := a[0]; // maximum value in the array (so far)
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal <= maxVal
    invariant forall k :: 0 <= k < i ==> minVal <= a[k]
    invariant exists k :: 0 <= k < i && minVal == a[k]
    invariant forall k :: 0 <= k < i ==> maxVal >= a[k]
    invariant exists k :: 0 <= k < i && maxVal == a[k]
  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  diff := maxVal - minVal;

  assert forall k :: 0 <= k < a.Length ==> minVal <= a[k];
  assert forall k :: 0 <= k < a.Length ==> maxVal >= a[k];
  assert exists k :: 0 <= k < a.Length && minVal == a[k];
  assert exists k :: 0 <= k < a.Length && maxVal == a[k];
  assert forall j, k :: 0 <= j < a.Length && 0 <= k < a.Length ==> a[j] - a[k] <= diff;
  assert exists j, k :: 0 <= j < a.Length && 0 <= k < a.Length && a[j] - a[k] == diff;
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
