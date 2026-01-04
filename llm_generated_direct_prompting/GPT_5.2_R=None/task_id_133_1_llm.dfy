
ghost function SumNegPrefix(a: array<int>, n: int): int
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then 0
  else
    SumNegPrefix(a, n - 1) + (if a[n - 1] < 0 then a[n - 1] else 0)
}

// Iterative implementatiom.
// Returns the sum of the negative numbers in an array 'a'.  
method CalcSumOfNegatives(a: array<int>) returns (result: int)
  ensures result == SumNegPrefix(a, a.Length)
{
  result := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant result == SumNegPrefix(a, i)
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
