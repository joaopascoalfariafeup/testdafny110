// Ghost function to compute the expected result sequence
// Processes from the end to match forward iteration
ghost function {:fuel 6} removeElems<T(==)>(a: seq<T>, b: seq<T>, seen: set<T>): seq<T>
{
  if a == [] then []
  else 
    var rest := removeElems(a[..|a|-1], b, seen);
    var last := a[|a|-1];
    var seenSoFar := seen + set x | x in a[..|a|-1];
    if last in b || last in seenSoFar then rest
    else rest + [last]
}

// Helper lemma to prove the relationship between iterations
lemma removeElemsAppend<T>(a: seq<T>, b: seq<T>, seen: set<T>, x: T)
  ensures removeElems(a + [x], b, seen) == 
    (var rest := removeElems(a, b, seen);
     var seenSoFar := seen + set y | y in a;
     if x in b || x in seenSoFar then rest else rest + [x])
{
  if a == [] {
    assert a + [x] == [x];
  } else {
    assert (a + [x])[..|a + [x]|-1] == a;
    assert (a + [x])[|a + [x]|-1] == x;
  }
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
    invariant res == removeElems(a[..i], b[..], {})
  {
    ghost var oldSeen := seen;
    ghost var oldRes := res;
    assert a[..i+1] == a[..i] + [a[i]];
    removeElemsAppend(a[..i], b[..], {}, a[i]);
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
  assert removeElems([1, 2, 1, 3], [1], {}) == [2, 3];
  assert |res1| <= 2;
  assert res1 == [2, 3] ;
  var res2 := RemoveElements(a2, a3);
  assert a2[..] == [1, 2, 1, 3, 2];
  assert 2 in res2 && 3 in res2;
  assert 1 !in res2;
  assert removeElems([1, 2, 1, 3, 2], [1], {}) == [2, 3];
  assert |res2| <= 2;
  assert res2 == [2, 3] ;
}

