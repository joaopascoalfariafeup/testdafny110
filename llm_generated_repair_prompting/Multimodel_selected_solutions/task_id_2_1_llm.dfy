// Obtains the set of elements (without duplicates) shared between two arrays. 
method SharedElements<T(==)>(a: array<T>, b: array<T>) returns (result: set<T>)
  ensures forall x :: x in result <==> (x in a[..] && x in b[..])
{
  result := {};
  for i := 0 to a.Length // loop through the first array
    invariant forall x :: x in result <==> (x in a[..i] && x in b[..])
  {
    if a[i] !in result && a[i] in b[..] {
      result := result + {a[i]};
    }
  }
}


// Test cases checked statically.
method SharedElementsTest(){
  // arrays with shared elements and no duplicates
  var a1:= new int[] [3, 4, 5, 6];
  var a2:= new int[] [5, 7, 4, 10];
  var res1 := SharedElements(a1, a2);
  assert a1[..] == [3, 4, 5, 6];
  assert a2[..] == [5, 7, 4, 10];
  assert res1 == {4, 5};

  // arrays with duplicates and shared elements 
  var a3:= new int[] [1, 3, 3, 4];
  var a4:= new int[] [4, 4, 3, 7];
  var res2 := SharedElements(a3, a4);
  assert a3[..] == [1, 3, 3, 4];
  assert a4[..] == [4, 4, 3, 7];
  assert res2 == {3, 4};

  // arrays with no shared elements
  var a5:= new int[] [11, 12, 13];
  var a6:= new int[] [17, 15, 14];
  var res3 := SharedElements(a5, a6);
  assert a5[..] == [11, 12, 13];
  assert a6[..] == [17, 15, 14];
  assert res3 == {};
}
