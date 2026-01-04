// Obtains the set of elements (without duplicates) shared between two arrays. 
method SharedElements<T(==)>(a: array<T>, b: array<T>) returns (result: set<T>)
  ensures result == elems(a[..]) * elems(b[..])
{
  result := {};
  for i := 0 to a.Length // loop through the first array
    invariant result == elems(a[..i]) * elems(b[..])
  {
    if a[i] !in result && a[i] in b[..] {
      result := result + {a[i]};
    }
  }
}

// Auxiliary function that returns the set of elements (without duplicates) in a sequence.
ghost function elems<T>(s: seq<T>) : set<T> {
  set x | x in s
}

// Test cases checked statically.
method SharedElementsTest(){
  // arrays with shared elements and no duplicates
  var a1:= new int[] [3, 4, 5, 6];
  var a2:= new int[] [5, 7, 4, 10];
  assert a1[1] == a2[2] == 4; // proof helper
  assert a1[2] == a2[0] == 5; // proof helper
  var res1 := SharedElements(a1, a2);
  assert res1 == {4, 5};

  // arrays with duplicates and shared elements 
  var a3:= new int[] [1, 3, 3, 4];
  var a4:= new int[] [4, 4, 3, 7];
  assert a3[1] == a4[2] == 3; // proof helper
  assert a3[3] == a4[0] == 4; // proof helper
  var res2 := SharedElements(a3, a4);
  assert res2 == {3, 4};

  // arrays with no shared elements
  var a5:= new int[] [11, 12, 13];
  var a6:= new int[] [17, 15, 14];
  var res3 := SharedElements(a5, a6);
  assert res3 == {};
}