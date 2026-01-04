method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures res == [x: int | x in a[..] && x < 0]
{
  res := [];
  for i := 0 to a.Length
    invariant res == [x: int | x in a[..i] && x < 0]
  {
    if a[i] < 0 {
      res := res + [a[i]];
    }
  }
}

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

