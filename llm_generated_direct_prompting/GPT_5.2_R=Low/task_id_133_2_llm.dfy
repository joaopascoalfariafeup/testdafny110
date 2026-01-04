
ghost function SumNeg(s: seq<int>): int
{
  if |s| == 0 then 0
  else SumNeg(s[..|s|-1]) + (if s[|s|-1] < 0 then s[|s|-1] else 0)
}

// Iterative implementatiom.
// Returns the sum of the negative numbers in an array 'a'.  
method CalcSumOfNegatives(a: array<int>) returns (result: int)
  ensures result == SumNeg(a[..])
{
  result := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant result == SumNeg(a[..i])
  {
    if a[i] < 0 {
      result := result + a[i];
    }
    assert result == SumNeg(a[..i+1]);
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
