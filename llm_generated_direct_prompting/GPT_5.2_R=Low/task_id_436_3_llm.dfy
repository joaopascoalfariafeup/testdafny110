// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
function FilterNeg(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else
    if s[|s|-1] < 0 then FilterNeg(s[..|s|-1]) + [s[|s|-1]]
    else FilterNeg(s[..|s|-1])
}

lemma FilterNegExtend(s: seq<int>, x: int)
  ensures FilterNeg(s + [x]) == (if x < 0 then FilterNeg(s) + [x] else FilterNeg(s))
{
}

method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures res == FilterNeg(a[..])
{
  res := [];
  for i := 0 to a.Length
    invariant res == FilterNeg(a[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    FilterNegExtend(a[..i], a[i]);
    if a[i] < 0 {
      res := res + [a[i]];
    }
  }
}


// Test cases checked statically.
method FindNegativeNumbersTest(){
  var a1 := new int[] [-1, 4, 5, -6];
  var res1 := FindNegativeNumbers(a1);
  assert res1 == [-1, -6];

  var a2:= new int[] [-1, -2, -3];
  var res2 := FindNegativeNumbers(a2);
  assert res2 == [-1, -2, -3];

  var a3:= new int[] [0, 1];
  var res3 := FindNegativeNumbers(a3);
  assert res3 == [];
}
