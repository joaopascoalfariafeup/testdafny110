
// Iterative implementatiom.
// Returns the sum of the negative numbers in an array 'a'.  
method CalcSumOfNegatives(a: array<int>) returns (result: int)
  ensures forall k :: 0 <= k < a.Length ==> a[k] >= 0 ==> result == old(result)
  ensures forall k :: 0 <= k < a.Length ==> a[k] < 0 ==> result == old(result) + a[k]
{
  result := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] >= 0 ==> result == old(result)
    invariant forall k :: 0 <= k < i ==> a[k] < 0 ==> result == old(result) + a[k]
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
