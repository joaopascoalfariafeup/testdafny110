// Obtains the element-wise subtraction of two arrays of integers of equal length.
method ElementWiseSubtraction(a: array<int>, b: array<int>) returns (result: array<int>)
  requires a.Length == b.Length
  ensures result.Length == a.Length
  ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] - b[i]
{
  result := new int[a.Length];
  for i := 0 to a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] - b[k]
  {
    result[i] := a[i] - b[i];
  }
}

method ElementWiseSubtractionTest(){
  var a1:= new int[] [1, 2, 3];
  var a2:= new int[] [4, 5, 6];
  var res1 := ElementWiseSubtraction(a1,a2);
  assert res1[..] == [-3, -3, -3];

  var a3:= new int[] [1, 2];
  var a4:= new int[] [3, 4];
  var res2 := ElementWiseSubtraction(a3,a4);
  assert res2[..] == [-2, -2];

  var a5:= new int[] [90, 120];
  var a6:= new int[] [50, 70];
  var res3 := ElementWiseSubtraction(a5,a6);
  assert res3[..] == [40, 50];
}