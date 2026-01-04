// Returns an array of the cubes of the elements of the input array.
method CubeElements(a: array<int>) returns (cubed: array<int>)
    ensures cubed.Length == a.Length
    ensures forall k :: 0 <= k < a.Length ==> cubed[k] == cube(a[k])
{
    cubed := new int[a.Length];
    for i := 0 to a.Length
        invariant cubed.Length == a.Length
        invariant forall k :: 0 <= k < i ==> cubed[k] == cube(a[k])
    {
        cubed[i] := cube(a[i]);
    }
}

function cube(x: int) : int {
     x * x * x
}


// Test cases checked statically.
method {:fuel cube,6} CubeElementsTest(){
  var a1 := new int[] [1, 2, 3, 4, 5];
  var res1 := CubeElements(a1);
  assert res1[..] == [1, 8, 27, 64, 125];

  var a2 := new int[] [2, 1, 0, -1, -2];
  var res2 := CubeElements(a2);
  assert res2[..] == [8, 1, 0, -1, -8];
}
