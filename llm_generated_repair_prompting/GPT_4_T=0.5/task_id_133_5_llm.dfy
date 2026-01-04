
function {:reads a} SumNegatives(a: array<int>, upto: nat): int
  requires upto <= a.Length
  reads a
{
  if upto == 0 then 0 
  else if a[upto-1] < 0 then a[upto-1] + SumNegatives(a, upto-1)
  else SumNegatives(a, upto-1)
}

method CalcSumOfNegatives(a: array<int>) returns (result: int)
  requires a.Length > 0
  ensures result == SumNegatives(a, a.Length)
{
  result := 0;
  for i := 0 to a.Length - 1
    invariant i <= a.Length
    invariant result == SumNegatives(a, i)
    invariant forall j :: 0 <= j < i ==> (a[j] < 0 ==> SumNegatives(a, j+1) == result + SumNegatives(a, j)) && (a[j] >= 0 ==> SumNegatives(a, j+1) == SumNegatives(a, j))
  {
    if a[i] < 0 {
      result := result + a[i];
    }
  }
}

method SumOfNegativesTest(){
  var a1 := new int[] [2, -6, -9];
  var a2 := new int[] [10, -14, 13];
  assert forall k :: 0 <= k < a1.Length ==> a1[k] == a1[k];
  assert forall k :: 0 <= k < a2.Length ==> a2[k] == a2[k];
  var out1 := CalcSumOfNegatives(a1);
  assert out1 == -15;
  var out2 := CalcSumOfNegatives(a2);
  assert out2 == -14;
}

