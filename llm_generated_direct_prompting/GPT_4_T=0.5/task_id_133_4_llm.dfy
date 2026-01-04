// Iterative implementatiom.
// Returns the sum of the negative numbers in an array 'a'.  
method CalcSumOfNegatives(a: array<int>) returns (result: int)
  ensures forall i :: 0 <= i < a.Length && a[i] < 0 ==> result <= a[i]
  ensures forall i :: 0 <= i < a.Length && a[i] >= 0 ==> result <= 0
{
  result := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i && a[j] < 0 ==> result <= a[j]
    invariant forall j :: 0 <= j < i && a[j] >= 0 ==> result <= 0
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
