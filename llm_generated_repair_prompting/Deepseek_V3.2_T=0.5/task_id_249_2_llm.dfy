// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures |res| <= a.Length
  ensures forall x :: x in res ==> x in a[..] && x in b[..]
  ensures forall x :: x in res ==> x !in res[..|res| - 1]
  ensures forall i: int :: 0 <= i < |res| ==> res[i] in a[..]
  ensures forall i: int :: 0 <= i < |res| ==> exists j: int :: 0 <= j < a.Length && a[j] == res[i] && (forall k: int :: 0 <= k < i ==> res[k] != a[j])
{
  res := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant |res| <= i
    invariant forall x :: x in res ==> x in a[..i] && x in b[..]
    invariant forall x :: x in res ==> x !in res[..|res| - 1]
    invariant forall k: int :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k: int :: 0 <= k < |res| ==> exists j: int :: 0 <= j < i && a[j] == res[k] && (forall l: int :: 0 <= l < k ==> res[l] != a[j])
  {
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      res := res + [a[i]];
    }
    i := i + 1;
  }
}

// Test cases checked statically
method IntersectionTest(){
  var a := new int[] [1, 2, 3];
  var b := new int[] [1, 3, 1];
  var c := new int[] [2, 4, 6];

  // Typical case
  var res1 := Intersection(a, b);
  // Provide helper assertions to help Dafny verify the test
  assert a[..] == [1, 2, 3];
  assert b[..] == [1, 3, 1];
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert b[..] == [1, 3, 1];
  assert c[..] == [2, 4, 6];
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert b[..] == [1, 3, 1];
  assert a[..] == [1, 2, 3];
  // The result should contain 1 and 3 in the order they appear in b
  // Since b has 1 at index 0 and 2, and 3 at index 1, the first occurrence of 1 is at index 0
  // So the result should be [1, 3]
  assert res3 == [1, 3];
}

