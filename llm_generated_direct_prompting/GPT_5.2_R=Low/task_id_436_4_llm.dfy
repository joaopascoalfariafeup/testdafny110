// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
function NegativesPrefix(a: array<int>, n: int): seq<int>
  requires 0 <= n <= a.Length
  reads a
  decreases n
{
  if n == 0 then []
  else if a[n-1] < 0 then NegativesPrefix(a, n-1) + [a[n-1]]
  else NegativesPrefix(a, n-1)
}

method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures res == NegativesPrefix(a, a.Length)
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == NegativesPrefix(a, i)
  {
    if a[i] < 0 {
      res := res + [a[i]];
      assert NegativesPrefix(a, i + 1) == NegativesPrefix(a, i) + [a[i]];
    } else {
      assert NegativesPrefix(a, i + 1) == NegativesPrefix(a, i);
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
