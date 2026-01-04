// Resturns a sequence with the negative numbers in the input array 'a', 
// by the same order as they appear in the array.
method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures forall x :: x in res ==> x < 0
  ensures forall i :: 0 <= i < a.Length ==> (a[i] < 0 ==> a[i] in res)
  ensures forall x :: x in res ==> (exists i :: 0 <= i < a.Length && a[i] == x)
  ensures forall i,j :: 0 <= i < j < a.Length ==> (a[i] < 0 && a[j] < 0 ==> exists p,q :: 0 <= p < q < |res| && res[p] == a[i] && res[q] == a[j])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in res ==> x < 0
    invariant forall j :: 0 <= j < i ==> (a[j] < 0 ==> a[j] in res)
    invariant forall x :: x in res ==> (exists j :: 0 <= j < i && a[j] == x)
    invariant forall j,k :: 0 <= j < k < i ==> (a[j] < 0 && a[k] < 0 ==> exists p,q :: 0 <= p < q < |res| && res[p] == a[j] && res[q] == a[k])
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
