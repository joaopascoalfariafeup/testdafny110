// Returns the sum of the minimum and maximum elements of a non-empty array
method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == (min i | 0 <= i < a.Length :: a[i]) + (max i | 0 <= i < a.Length :: a[i])
{
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal == (min j | 0 <= j < i :: a[j])
    invariant maxVal == (max j | 0 <= j < i :: a[j])
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

