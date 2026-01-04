// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == a[..] && b[..] // The result is a sequence with elements that belong to both arrays
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..] && res[k] in b[..] // All elements in the result are in both input arrays
  ensures forall k, l :: 0 <= k < l < |res| ==> res[k] != res[l] // No duplicates in the result
  ensures forall k :: 0 <= k < |a| ==> (a[k] in b[..] && a[k] !in res[0..k] ==> a[k] in res[k..]) // Ordering of elements in the result follows the first array
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length // i is within the bounds of the array a
    invariant res == a[..i] && b[..] // The result is a sequence with elements that belong to both arrays up to index i
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i] && res[k] in b[..] // All elements in the result are in both input arrays up to index i
    invariant forall k, l :: 0 <= k < l < |res| ==> res[k] != res[l] // No duplicates in the result up to index i
    invariant forall k :: 0 <= k < i ==> (a[k] in b[..] && a[k] !in res[0..k] ==> a[k] in res[k..]) // Ordering of elements in the result follows the first array up to index i
  {
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
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
