// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures forall j :: 0 <= j < |res| ==> res[j] < 0
  ensures forall i :: 0 <= i < a.Length ==> (a[i] < 0 ==> exists j :: 0 <= j < |res| && res[j] == a[i])
  ensures forall j :: 0 <= j < |res| ==> exists i :: 0 <= i < a.Length && a[i] == res[j]
  ensures forall i, j :: 0 <= i < j < |res| ==>
            (exists ii, jj :: 0 <= ii < jj < a.Length && a[ii] == res[i] && a[jj] == res[j])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < |res| ==> res[j] < 0
    invariant forall k :: 0 <= k < i ==> (a[k] < 0 ==> exists j :: 0 <= j < |res| && res[j] == a[k])
    invariant forall j :: 0 <= j < |res| ==> exists k :: 0 <= k < i && a[k] == res[j]
    invariant forall p, q :: 0 <= p < q < |res| ==>
              (exists ii, jj :: 0 <= ii < jj < i && a[ii] == res[p] && a[jj] == res[q])
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
