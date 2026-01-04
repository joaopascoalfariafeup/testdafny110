// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures forall i, j :: 0 <= i < j < a.Length ==> (a[i] in res ==> a[i] != a[j])
  ensures forall i :: 0 <= i < a.Length ==> (a[i] in res ==> a[i] !in b[..]) 
  ensures forall i :: 0 <= i < |res| ==> res[i] in a[..] && res[i] !in b[..] && res[i] !in a[..i]
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> (a[k] in res ==> a[k] !in b[..]) 
    invariant forall k :: 0 <= k < i ==> (a[k] in res ==> a[k] !in a[..k])
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..] && res[k] !in b[..] && res[k] !in a[..k]
  {
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }
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
