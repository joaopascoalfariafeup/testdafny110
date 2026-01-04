
// Ghost function to compute the expected result sequence
ghost function {:fuel 30} removeElems<T(==)>(a: seq<T>, b: seq<T>): seq<T>
{
  if a == [] then []
  else if a[|a|-1] in b || a[|a|-1] in a[..|a|-1] then removeElems(a[..|a|-1], b)
  else removeElems(a[..|a|-1], b) + [a[|a|-1]]
}

// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures forall x :: x in res ==> x in a[..] && x !in b[..]
  ensures forall x :: x in a[..] && x !in b[..] ==> x in res
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[i]
  ensures res == removeElems(a[..], b[..])
{
  res := [];
  for i := 0 to a.Length
    invariant forall x :: x in res ==> x in a[..i] && x !in b[..]
    invariant forall x :: x in a[..i] && x !in b[..] ==> x in res
    invariant forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
    invariant forall j :: 0 <= j < |res| ==> exists k :: 0 <= k < i && a[k] == res[j]
    invariant res == removeElems(a[..i], b[..])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
  assert a[..] == a[..a.Length];
}




// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);
  assert a1[..] == [1, 2, 3, 4];
  assert a2[..] == [2, 4];
  assert res1 == removeElems([1, 2, 3, 4], [2, 4]);
  // Step by step unfolding
  assert removeElems<int>([], [2, 4]) == [];
  assert 1 !in [2, 4] && 1 !in [];
  assert removeElems([1], [2, 4]) == [] + [1];
  assert removeElems([1], [2, 4]) == [1];
  assert 2 in [2, 4];
  assert removeElems([1, 2], [2, 4]) == removeElems([1], [2, 4]);
  assert removeElems([1, 2], [2, 4]) == [1];
  assert 3 !in [2, 4] && 3 !in [1, 2];
  assert removeElems([1, 2, 3], [2, 4]) == removeElems([1, 2], [2, 4]) + [3];
  assert removeElems([1, 2, 3], [2, 4]) == [1] + [3];
  assert removeElems([1, 2, 3], [2, 4]) == [1, 3];
  assert 4 in [2, 4];
  assert removeElems([1, 2, 3, 4], [2, 4]) == removeElems([1, 2, 3], [2, 4]);
  assert removeElems([1, 2, 3, 4], [2, 4]) == [1, 3];
  assert res1 == [1, 3];
}

  // Boundary cases
method RemoveElementsEmpty(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [];
  var res2 := RemoveElements(a1, a1);
  assert a1[..] == [1, 2, 3, 4];
  assert res2 == removeElems([1, 2, 3, 4], [1, 2, 3, 4]);
  assert removeElems<int>([], [1, 2, 3, 4]) == [];
  assert 1 in [1, 2, 3, 4];
  assert removeElems([1], [1, 2, 3, 4]) == removeElems<int>([], [1, 2, 3, 4]);
  assert removeElems([1], [1, 2, 3, 4]) == [];
  assert 2 in [1, 2, 3, 4];
  assert removeElems([1, 2], [1, 2, 3, 4]) == removeElems([1], [1, 2, 3, 4]);
  assert removeElems([1, 2], [1, 2, 3, 4]) == [];
  assert 3 in [1, 2, 3, 4];
  assert removeElems([1, 2, 3], [1, 2, 3, 4]) == removeElems([1, 2], [1, 2, 3, 4]);
  assert removeElems([1, 2, 3], [1, 2, 3, 4]) == [];
  assert 4 in [1, 2, 3, 4];
  assert removeElems([1, 2, 3, 4], [1, 2, 3, 4]) == removeElems([1, 2, 3], [1, 2, 3, 4]);
  assert removeElems([1, 2, 3, 4], [1, 2, 3, 4]) == [];
  assert res2 == [];
  var res3 := RemoveElements(a1, a2);
  assert a2[..] == [];
  assert res3 == removeElems([1, 2, 3, 4], []);
  // Add intermediate assertions to help Dafny unfold the recursion
  var emptySeq: seq<int> := [];
  assert removeElems<int>([], emptySeq) == [];
  assert 1 !in emptySeq && 1 !in emptySeq;
  assert removeElems([1], emptySeq) == [] + [1] == [1];
  assert 2 !in emptySeq && 2 !in [1];
  assert removeElems([1, 2], emptySeq) == [1] + [2] == [1, 2];
  assert 3 !in emptySeq && 3 !in [1, 2];
  assert removeElems([1, 2, 3], emptySeq) == [1, 2] + [3] == [1, 2, 3];
  assert 4 !in emptySeq && 4 !in [1, 2, 3];
  assert removeElems([1, 2, 3, 4], emptySeq) == [1, 2, 3] + [4] == [1, 2, 3, 4];
  assert res3 == [1, 2, 3, 4];
}


// Duplicates in the first array
method RemoveElementsDups(){
  var a1 := new int[] [1, 2, 1, 3];
  var a2 := new int[] [1, 2, 1, 3, 2];
  var a3 := new int[] [1];
  var res1 := RemoveElements(a1, a3);
  assert a1[..] == [1, 2, 1, 3];
  assert a3[..] == [1];
  assert res1 == removeElems([1, 2, 1, 3], [1]);
  // Add intermediate assertions to help Dafny
  assert removeElems<int>([], [1]) == [];
  assert 1 in [1];
  assert removeElems([1], [1]) == removeElems<int>([], [1]);
  assert removeElems([1], [1]) == [];
  assert 2 !in [1] && 2 !in [1];
  assert removeElems([1, 2], [1]) == removeElems([1], [1]) + [2];
  assert removeElems([1, 2], [1]) == [] + [2];
  assert removeElems([1, 2], [1]) == [2];
  assert 1 in [1];
  assert removeElems([1, 2, 1], [1]) == removeElems([1, 2], [1]);
  assert removeElems([1, 2, 1], [1]) == [2];
  assert 3 !in [1] && 3 !in [1, 2, 1];
  assert removeElems([1, 2, 1, 3], [1]) == removeElems([1, 2, 1], [1]) + [3];
  assert removeElems([1, 2, 1, 3], [1]) == [2] + [3];
  assert removeElems([1, 2, 1, 3], [1]) == [2, 3];
  assert res1 == [2, 3] ;
  var res2 := RemoveElements(a2, a3);
  assert a2[..] == [1, 2, 1, 3, 2];
  assert res2 == removeElems([1, 2, 1, 3, 2], [1]);
  // 2 is in [1, 2, 1, 3] so it's a duplicate
  assert 2 in [1, 2, 1, 3];
  assert removeElems([1, 2, 1, 3, 2], [1]) == removeElems([1, 2, 1, 3], [1]);
  assert removeElems([1, 2, 1, 3, 2], [1]) == [2, 3];
  assert res2 == [2, 3] ;
}



