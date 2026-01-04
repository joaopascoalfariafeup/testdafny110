// Checks if all elements in an array are equal to a given number.
method AllElementsEqualTo<T(==)>(a: array<T>, x: T) returns (result: bool)
  ensures result <==> (forall i:int :: 0 <= i < a.Length ==> a[i] == x)
{
  for i := 0 to a.Length
    invariant forall k:int :: 0 <= k < i ==> a[k] == x
  {
    if a[i] != x {
      assert !(forall j:int :: 0 <= j < a.Length ==> a[j] == x) by {
        assume H: forall j:int :: 0 <= j < a.Length ==> a[j] == x;
        assert 0 <= i < a.Length;
        assert a[i] == x;
      }
      return false;
    }
  }
  return true;
}

method AllElementsEqualTest(){
  var a1:= new int[] [1, 3, 5, 7, 9, 2, 4, 6, 8];
  var res1:=AllElementsEqualTo(a1, 3);
  assert !res1;

  var a2:= new int[] [1,1,1,1,1,1,1];
  var res2:=AllElementsEqualTo(a2, 1);
  assert res2;

  var a3 := new int[] [5,6,7,4,8];
  var res3 := AllElementsEqualTo(a3, 6);
  assert a3[2] != 6;
  assert !res3;
}

