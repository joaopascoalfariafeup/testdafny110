
ghost function SumNeg(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else SumNeg(s[..|s|-1]) + (if s[|s|-1] < 0 then s[|s|-1] else 0)
}

lemma SumNegExtend(s: seq<int>, x: int)
  ensures SumNeg(s + [x]) == SumNeg(s) + (if x < 0 then x else 0)
{
  if |s| == 0 {
    assert (s + [x])[..|(s + [x])|-1] == [];
  } else {
    assert (s + [x])[..|(s + [x])|-1] == s;
  }
  assert (s + [x])[|s + [x]| - 1] == x;
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
    ghost var r0 := result;
    if a[i] < 0 {
      result := result + a[i];
    }
    assert result == r0 + (if a[i] < 0 then a[i] else 0);
    assert a[..i+1] == a[..i] + [a[i]];
    SumNegExtend(a[..i], a[i]);
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
