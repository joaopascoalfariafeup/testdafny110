// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures |res| <= a.Length
  ensures forall k :: 0 <= k < |res| ==> res[k] < 0
  ensures forall k :: 0 <= k < a.Length && a[k] < 0 ==> a[k] in res
  ensures forall i, j :: 0 <= i < j < a.Length && a[i] < 0 && a[j] < 0 ==> 
    exists idx_i, idx_j :: 0 <= idx_i < idx_j < |res| && res[idx_i] == a[i] && res[idx_j] == a[j]
{
  res := [];
  for i := 0 to a.Length
    invariant |res| <= i
    invariant forall k :: 0 <= k < |res| ==> res[k] < 0
    invariant forall k :: 0 <= k < i && a[k] < 0 ==> a[k] in res
    invariant forall p, q :: 0 <= p < q < i && a[p] < 0 && a[q] < 0 ==> 
      exists idx_p, idx_q :: 0 <= idx_p < idx_q < |res| && res[idx_p] == a[p] && res[idx_q] == a[q]
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
