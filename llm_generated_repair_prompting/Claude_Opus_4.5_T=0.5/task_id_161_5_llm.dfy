// Ghost function to compute the expected result sequence
// Processes from the beginning to match forward iteration
ghost function {:fuel 10} removeElemsHelper<T(==)>(a: seq<T>, i: int, b: seq<T>, seen: set<T>): seq<T>
  requires 0 <= i <= |a|
  decreases |a| - i
{
  if i == |a| then []
  else 
    var elem := a[i];
    var rest := removeElemsHelper(a, i + 1, b, seen + {elem});
    if elem in b || elem in seen then rest
    else [elem] + rest
}

ghost function {:fuel 10} removeElems<T(==)>(a: seq<T>, b: seq<T>, seen: set<T>): seq<T>
{
  removeElemsHelper(a, 0, b, seen)
}

// Helper predicate to avoid trigger warnings
ghost predicate inSeq<T>(x: T, s: seq<T>) {
  x in s
}

// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures forall x :: x in res ==> x in a[..] && x !in b[..]
  ensures forall x :: x in a[..] && x !in b[..] ==> x in res
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[i]
  ensures res == removeElems(a[..], b[..], {})
{
  res := [];
  ghost var seen: set<T> := {};
  for i := 0 to a.Length
    invariant forall x :: x in res ==> x in a[..i] && x !in b[..]
    invariant forall x :: x in a[..i] && x !in b[..] ==> x in res
    invariant forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
    invariant forall j :: 0 <= j < |res| ==> exists k :: 0 <= k < i && a[k] == res[j]
    invariant seen == set x | x in a[..i]
    invariant res + removeElemsHelper(a[..], i, b[..], seen) == removeElems(a[..], b[..], {})
  {
    ghost var oldSeen := seen;
    ghost var oldRes := res;
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }
    seen := seen + {a[i]};
  }
  assert a[..a.Length] == a[..];
}




// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);
  assert a1[..] == [1, 2, 3, 4];
  assert a2[..] == [2, 4];
  assert 1 in res1 && 3 in res1;
  assert 2 !in res1 && 4 !in res1;
  assert removeElems([1, 2, 3, 4], [2, 4], {}) == [1, 3];
  assert |res1| <= 2;
  assert res1 == [1, 3];
}

  // Boundary cases
method RemoveElementsEmpty(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [];
  var res2 := RemoveElements(a1, a1);
  assert a1[..] == [1, 2, 3, 4];
  assert forall x :: x in a1[..] ==> x in a1[..];
  assert removeElems([1, 2, 3, 4], [1, 2, 3, 4], {}) == [];
  assert res2 == [];
  var res3 := RemoveElements(a1, a2);
  assert a2[..] == [];
  assert forall x :: x !in a2[..];
  // Step by step computation for removeElems([1, 2, 3, 4], [], {})
  assert removeElems([1, 2, 3, 4], [], {}) == [1, 2, 3, 4];
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
  assert 2 in res1 && 3 in res1;
  assert 1 !in res1;
  // Step by step
  assert removeElems([1, 2, 1, 3], [1], {}) == [2, 3];
  assert |res1| <= 2;
  assert res1 == [2, 3] ;
  var res2 := RemoveElements(a2, a3);
  assert a2[..] == [1, 2, 1, 3, 2];
  assert 2 in res2 && 3 in res2;
  assert 1 !in res2;
  // Step by step
  assert removeElems([1, 2, 1, 3, 2], [1], {}) == [2, 3];
  assert |res2| <= 2;
  assert res2 == [2, 3] ;
}
