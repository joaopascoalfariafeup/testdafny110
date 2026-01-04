// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures exists i:int, j:int :: 0 <= i < a.Length && 0 <= j < a.Length && sum == a[i] + a[j]
  ensures forall k:int :: 0 <= k < a.Length ==> (exists j:int :: 0 <= j < a.Length && sum <= a[k] + a[j])
  ensures forall k:int :: 0 <= k < a.Length ==> (exists j:int :: 0 <= j < a.Length && a[k] + a[j] <= sum)
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant exists p:int :: 0 <= p < i && minVal == a[p]
    invariant exists q:int :: 0 <= q < i && maxVal == a[q]
    invariant forall k:int :: 0 <= k < i ==> minVal <= a[k]
    invariant forall k:int :: 0 <= k < i ==> a[k] <= maxVal
  {
    if a[i] < minVal {
      minVal := a[i];
    }
    if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  sum := minVal + maxVal;
}

// Test cases checked statically.
method SumMinMaxTest(){
  var a1 := new int[] [1,2,3];
  assert a1[..] == [1,2,3];
  var out1 := SumMinMax(a1);
  assert out1 == 4;

  var a2 := new int[] [-1,2,3,4];
  assert a2[..] == [-1,2,3,4];
  var out2 := SumMinMax(a2);
  assert out2 == 3;

  var a3 := new int[] [2,3,6];
  assert a3[..] == [2,3,6];
  var out3 := SumMinMax(a3);
  assert out3 == 8;
}
