// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.

function {:fuel 50} SeqIntersection<T(==)>(as: seq<T>, bs: seq<T>): seq<T>
{
  if |as| == 0 then []
  else
    var r := SeqIntersection(as[..|as|-1], bs);
    if as[|as|-1] in bs && as[|as|-1] !in r then r + [as[|as|-1]] else r
}

method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == SeqIntersection(a[..], b[..])
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..] && res[k] in b[..]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == SeqIntersection(a[..i], b[..])
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
