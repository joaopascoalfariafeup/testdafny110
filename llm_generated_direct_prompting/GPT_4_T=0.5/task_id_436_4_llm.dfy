// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures forall k :: 0 <= k < |res| ==> res[k] < 0 
  ensures forall k :: 0 <= k < a.Length ==> (a[k] < 0 ==> a[k] in res) 
  ensures forall k :: 0 <= k < |res| ==> (res[k] in a && res[k] < 0)
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> (a[k] < 0 ==> a[k] in res)
    invariant forall k :: 0 <= k < |res| ==> (res[k] in a && res[k] < 0)
  {
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
