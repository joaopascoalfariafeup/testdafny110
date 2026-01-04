
// Auxiliary ghost function to compute sum of negatives in a sequence
ghost function SumOfNegatives(s: seq<int>): int
{
  if |s| == 0 then 0
  else (if s[|s|-1] < 0 then s[|s|-1] else 0) + SumOfNegatives(s[..|s|-1])
}

// Iterative implementatiom.
// Returns the sum of the negative numbers in an array 'a'.  
method CalcSumOfNegatives(a: array<int>) returns (result: int)
  ensures result == SumOfNegatives(a[..])
{
  result := 0;
  for i := 0 to a.Length
    invariant result == SumOfNegatives(a[..i])
  {
    if a[i] < 0 {
      result := result + a[i];
    }
    assert a[..i+1] == a[..i] + [a[i]];
  }
  assert a[..a.Length] == a[..];
}

// Test cases checked statically.
method SumOfNegativesTest(){
  var a1 := new int[] [2, -6, -9];
  var out1 := CalcSumOfNegatives(a1);
  assert a1[..] == [2, -6, -9];
  assert {:fuel SumOfNegatives, 4} out1 == -15;

  var a2 := new int[] [10, -14, 13];
  var out2 := CalcSumOfNegatives(a2);
  assert a2[..] == [10, -14, 13];
  assert {:fuel SumOfNegatives, 4} out2 == -14;
}
