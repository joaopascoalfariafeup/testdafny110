// Checks if all elements in an array are equal to a given number.
method AllElementsEqualTo<T(==)>(a: array<T>, x: T) returns (result: bool)
  ensures result == (forall i :: 0 <= i < a.Length ==> a[i] == x)
{
  var idx := 0;
  while idx < a.Length
    invariant 0 <= idx <= a.Length
    invariant forall j :: 0 <= j < idx ==> a[j] == x
  {
    if a[idx] != x {
      return false;
    }
    idx := idx + 1;
  }
  return true;
}

method AllElementsEqualTest(){
  var a1:= new int[] [1, 3, 5, 7, 9, 2, 4, 6, 8];
  // Help Dafny know the array contents
  assert a1[0] == 1 && a1[1] == 3 && a1[2] == 5 && a1[3] == 7 && a1[4] == 9 && 
         a1[5] == 2 && a1[6] == 4 && a1[7] == 6 && a1[8] == 8;
  var res1:=AllElementsEqualTo(a1, 3);
  assert !res1;

  var a2:= new int[] [1,1,1,1,1,1,1];
  // Help Dafny know the array contents
  assert a2[0] == 1 && a2[1] == 1 && a2[2] == 1 && a2[3] == 1 && 
         a2[4] == 1 && a2[5] == 1 && a2[6] == 1;
  var res2:=AllElementsEqualTo(a2, 1);
  assert res2;

  var a3 := new int[] [5,6,7,4,8];
  // Help Dafny know the array contents
  assert a3[0] == 5 && a3[1] == 6 && a3[2] == 7 && a3[3] == 4 && a3[4] == 8;
  var res3 := AllElementsEqualTo(a3, 6);
  assert a3[2] != 6;
  assert !res3;
}
