// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures exists i :: 0 <= i < a.Length && a[i] + a[i] == sum ==> a.Length == 1
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] + a[j] == sum
  ensures forall k :: 0 <= k < a.Length ==> sum <= a[k] + a[k] || sum >= a[k] + a[k]
  ensures (exists i :: 0 <= i < a.Length && forall k :: 0 <= k < a.Length ==> a[i] <= a[k]) &&
          (exists j :: 0 <= j < a.Length && forall k :: 0 <= k < a.Length ==> a[j] >= a[k]) &&
          (exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length &&
              (forall k :: 0 <= k < a.Length ==> a[i] <= a[k]) &&
              (forall k :: 0 <= k < a.Length ==> a[j] >= a[k]) &&
              sum == a[i] + a[j])
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant exists p :: 0 <= p < i && minVal == a[p]
    invariant exists q :: 0 <= q < i && maxVal == a[q]
    invariant forall k :: 0 <= k < i ==> minVal <= a[k]
    invariant forall k :: 0 <= k < i ==> maxVal >= a[k]
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
  var out1 := SumMinMax(a1);
  assert out1 == 4;

  var a2 := new int[] [-1,2,3,4];
  var out2 := SumMinMax(a2);
  assert out2 == 3;

  var a3 := new int[] [2,3,6];
  var out3 := SumMinMax(a3);
  assert out3 == 8;
}

