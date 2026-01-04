// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures forall i :: 0 <= i < |res| ==> (res[i] in a[..] && res[i] in b[..] && forall j :: 0 <= j < i ==> res[j] != res[i])
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j] ==> a[i] in res
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < |res| ==> (res[k] in a[..] && res[k] in b[..] && forall j :: 0 <= j < k ==> res[j] != res[k])
    invariant forall k, j :: 0 <= k < i && 0 <= j < b.Length && a[k] == b[j] ==> a[k] in res
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
