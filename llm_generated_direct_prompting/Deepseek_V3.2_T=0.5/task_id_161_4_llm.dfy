// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  requires a != null && b != null
  ensures |res| <= a.Length
  ensures forall i :: 0 <= i < |res| ==> res[i] in a[..]
  ensures forall i :: 0 <= i < |res| ==> res[i] !in b[..]
  ensures forall i :: 0 <= i < |res| ==> res[i] !in res[..i]
  ensures forall x :: x in a[..] && x !in b[..] ==> x in res
  ensures forall i, j :: 0 <= i < j < |res| ==> exists k, l :: 0 <= k < l < a.Length && a[k] == res[i] && a[l] == res[j]
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant |res| <= i
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k :: 0 <= k < |res| ==> res[k] !in b[..]
    invariant forall k :: 0 <= k < |res| ==> res[k] !in res[..k]
    invariant forall x :: x in a[..i] && x !in b[..] ==> x in res
    invariant forall k, l :: 0 <= k < l < |res| ==> exists m, n :: 0 <= m < n < i && a[m] == res[k] && a[n] == res[l]
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

