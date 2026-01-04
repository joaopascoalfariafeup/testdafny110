// Returns an array of the same length as the input array, 
// with each element of the input array squared.
method SquareElements(a: array<int>) returns (squared: array<int>)
  ensures squared.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> squared[i] == a[i] * a[i]
{
  squared := new int[a.Length];
  for i := 0 to a.Length
    invariant forall k :: 0 <= k < i ==> squared[k] == a[k] * a[k]
  {
    squared[i] := a[i] * a[i];
  }
}

// Test cases checked statically
method SquareElementsTest(){
  // Typical case
  var a1 := new int[] [1, 2, 3, 4, 5];
  var res1 := SquareElements(a1);
  assert res1[..] ==  [1, 4, 9, 16, 25];

  // Boundary case - single element
  var a2 := new int[] [0];
  var res2 := SquareElements(a2);
  assert res2[..] == [0];

  // Boundary case - empty array
  var a3 := new int[] [];
  var res3:=SquareElements(a3);
  assert res3[..] == [];
}