
method SharedElements<T(==)>(a: array<T>, b: array<T>) returns (result: set<T>)
  ensures forall x :: x in result <==> (x in a[..] && x in b[..])
{
  result := {};
  for i := 0 to a.Length // loop through the first array
    invariant forall x :: x in result <==> ((x in a[..i]) && (x in b[..]))
  {
    if a[i] !in result && a[i] in b[..] {
      result := result + {a[i]};
    }
  }
}

method SharedElementsTest(){
  var a1:= new int[] [3, 4, 5, 6];
  var a2:= new int[] [5, 7, 4, 10];
  var res1 := SharedElements(a1, a2);
  assert 4 in res1 && 5 in res1 && |res1| == 2;

  var a3:= new int[] [1, 3, 3, 4];
  var a4:= new int[] [4, 4, 3, 7];
  var res2 := SharedElements(a3, a4);
  assert 3 in res2 && 4 in res2 && |res2| == 2;

  var a5:= new int[] [11, 12, 13];
  var a6:= new int[] [17, 15, 14];
  var res3 := SharedElements(a5, a6);
  assert res3 == {};
}

