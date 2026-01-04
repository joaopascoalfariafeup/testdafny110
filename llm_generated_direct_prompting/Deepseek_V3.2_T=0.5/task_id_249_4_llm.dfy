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
  for i := 0 to a.Length
    invariant |res| <= i
    invariant forall x :: x in res ==> x in a[..] && x in b[..]
    invariant forall x :: x in res ==> x !in res[..|res| - 1]
    invariant forall k: int :: 0 <= k < |res| ==> res[k] in a[..]
    invariant forall k: int :: 0 <= k < |res| ==> exists j: int :: 0 <= j < i && a[j] == res[k] && (forall l: int :: 0 <= l < k ==> res[l] != a[j])
  {
    if a[i] in b[..] && a[i] !in res {
      res := res + [a[i]];
    }
  }
}

// Test cases checked statically
method IntersectionTest(){
  var a := new int[] [1, 2, 3];
  var b := new int[] [1, 3, 1];
  var c := new int[] [2, 4, 6];

  // Typical case
  var res1 := Intersection(a, b);
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert res3 == [1, 3] || res3 == [3, 1];
}
