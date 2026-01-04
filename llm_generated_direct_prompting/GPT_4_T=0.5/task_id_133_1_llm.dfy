
// Iterative implementatiom.
// Returns the sum of the negative numbers in an array 'a'.  
method CalcSumOfNegatives(a: array<int>) returns (result: int)
  ensures forall k :: 0 <= k < a.Length && a[k] < 0 ==> result <= a[k] 
  ensures forall k :: 0 <= k < a.Length && a[k] >= 0 ==> result <= 0
  ensures forall k1, k2 :: 0 <= k1 < k2 < a.Length && a[k1] < 0 && a[k2] < 0 ==> result <= a[k1] + a[k2]
{
  result := 0;
  for i := 0 to a.Length
    invariant forall k :: 0 <= k < i && a[k] < 0 ==> result <= a[k] 
    invariant forall k :: 0 <= k < i && a[k] >= 0 ==> result <= 0
    invariant forall k1, k2 :: 0 <= k1 < k2 < i && a[k1] < 0 && a[k2] < 0 ==> result <= a[k1] + a[k2]
  {
    if a[i] < 0 {
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
