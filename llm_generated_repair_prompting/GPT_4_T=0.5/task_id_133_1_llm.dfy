
function SumNegatives(a: array<int>, upto: nat): int
  requires upto <= a.Length
{
  if upto == 0 then 0 
  else if a[upto-1] < 0 then a[upto-1] + SumNegatives(a, upto-1)
  else SumNegatives(a, upto-1)
}

// Iterative implementation.
// Returns the sum of the negative numbers in an array 'a'.  
method CalcSumOfNegatives(a: array<int>) returns (result: int)
  ensures result == SumNegatives(a, a.Length)
{
  result := 0;
  for i := 0 to a.Length
    invariant i <= a.Length
    invariant result == SumNegatives(a, i)
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

