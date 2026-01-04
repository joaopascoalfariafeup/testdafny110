// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.

function Negatives(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if s[|s|-1] < 0 then Negatives(s[..|s|-1]) + [s[|s|-1]]
  else Negatives(s[..|s|-1])
}

lemma NegativesExtend(s: seq<int>, x: int)
  ensures Negatives(s + [x]) == (if x < 0 then Negatives(s) + [x] else Negatives(s))
{
}

method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures res == Negatives(a[..])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == Negatives(a[..i])
  {
    ghost var r0 := res;
    if a[i] < 0 {
      res := res + [a[i]];
      assert res == r0 + [a[i]];
    } else {
      assert res == r0;
    }

    assert a[..i+1] == a[..i] + [a[i]];
    NegativesExtend(a[..i], a[i]);
    assert res == Negatives(a[..i+1]);
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
