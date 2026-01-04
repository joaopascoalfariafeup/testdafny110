// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures res == Filter(a[..], x => x < 0)
{
  res := [];
  for i := 0 to a.Length
    invariant res == Filter(a[..i], x => x < 0)
  {
    assert a[..i+1] == a[..i] + [a[i]]; // proof helper
    if a[i] < 0 {
      res := res + [a[i]];
    }
  }
  assert a[..] == a[..a.Length]; // proof helper
}

// Select from a sequence 'a' the elements that satisfy a predicate 'p'.
ghost function {:fuel 4} Filter<T>(a: seq<T>, p: (T) -> bool): seq<T> {
  if |a| == 0 then []
  else if p(a[|a|-1]) then Filter(a[..|a|-1], p) + [a[|a|-1]]
  else Filter(a[..|a|-1], p)
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