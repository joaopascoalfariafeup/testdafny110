// Helper function to extract negative numbers from a sequence
ghost function NegativesInSeq(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if s[|s|-1] < 0 then NegativesInSeq(s[..|s|-1]) + [s[|s|-1]]
  else NegativesInSeq(s[..|s|-1])
}

// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures res == NegativesInSeq(a[..])
{
  res := [];
  for i := 0 to a.Length
    invariant res == NegativesInSeq(a[..i])
  {
    if a[i] < 0 {
      assert a[..i+1] == a[..i] + [a[i]];
      res := res + [a[i]];
    } else {
      assert a[..i+1] == a[..i] + [a[i]];
    }
  }
  assert a[..a.Length] == a[..];
}


// Test cases checked statically.
method FindNegativeNumbersTest(){
  var a1 := new int[] [-1, 4, 5, -6];
  var res1 := FindNegativeNumbers(a1);
  assert a1[..] == [-1, 4, 5, -6];
  assert {:fuel NegativesInSeq, 5} res1 == [-1, -6];

  var a2:= new int[] [-1, -2, -3];
  var res2 := FindNegativeNumbers(a2);
  assert a2[..] == [-1, -2, -3];
  assert {:fuel NegativesInSeq, 4} res2 == [-1, -2, -3];

  var a3:= new int[] [0, 1];
  var res3 := FindNegativeNumbers(a3);
  assert a3[..] == [0, 1];
  assert {:fuel NegativesInSeq, 3} res3 == [];
}
