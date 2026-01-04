
// Iterative implementatiom.
// Returns the sum of the negative numbers in an array 'a'.  
method CalcSumOfNegatives(a: array<int>) returns (result: int)
  ensures forall k :: 0 <= k < a.Length ==> a[k] >= 0 ==> result == 0
  ensures forall k :: 0 <= k < a.Length ==> a[k] < 0 ==> result <= 0
  ensures result == sum{ k: int | 0 <= k < a.Length && a[k] < 0 :: a[k] }
{
  result := 0;
  var sum := 0;
  for i := 0 to a.Length
    invariant sum == sum{ k: int | 0 <= k < i && a[k] < 0 :: a[k] }
    invariant result == sum
  {
    if a[i] < 0 {
      sum := sum + a[i];
      result := result + a[i];
    }
  }
}

// Test cases checked statically.
method SumOfNegativesTest(){
  var a1 := new int[] [2, -6, -9];
  var out1 := CalcSumOfNegatives(a1);
  assert out1 == -15;

  var a2 := new int[] [10, -14, 13];
  var out2 := CalcSumOfNegatives(a2);
  assert out2 == -14;
}
