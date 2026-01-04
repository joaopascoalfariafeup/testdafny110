// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
function RemoveElementsSpec<T(==)>(a: seq<T>, b: seq<T>): seq<T>
  decreases |a|
{
  if |a| == 0 then
    []
  else
    var prev := RemoveElementsSpec(a[..|a|-1], b);
    var x := a[|a|-1];
    if x !in b && x !in a[..|a|-1] then prev + [x] else prev
}

method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == RemoveElementsSpec(a[..], b[..])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == RemoveElementsSpec(a[..i], b[..])
  {
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }
    assert res == RemoveElementsSpec(a[..i+1], b[..]);
  }
}




// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);
  assert res1 == [1, 3];
}

  // Boundary cases
method RemoveElementsEmpty(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [];
  var res2 := RemoveElements(a1, a1);
  assert res2 == [];
  var res3 := RemoveElements(a1, a2);
  assert res3 == [1, 2, 3, 4];
}


// Duplicates in the first array
method RemoveElementsDups(){
  var a1 := new int[] [1, 2, 1, 3];
  var a2 := new int[] [1, 2, 1, 3, 2];
  var a3 := new int[] [1];
  var res1 := RemoveElements(a1, a3);
  assert res1 == [2, 3] ;
  var res2 := RemoveElements(a2, a3);
  assert res2 == [2, 3] ;
}

