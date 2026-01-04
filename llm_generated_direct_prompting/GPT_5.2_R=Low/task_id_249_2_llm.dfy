// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
function {:fuel 20} IntersectSeq<T(==)>(sa: seq<T>, sb: seq<T>): seq<T>
{
  if |sa| == 0 then
    []
  else
    var r := IntersectSeq(sa[..|sa|-1], sb);
    if sa[|sa|-1] in sb && sa[|sa|-1] !in r then r + [sa[|sa|-1]] else r
}

method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == IntersectSeq(a[..], b[..])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == IntersectSeq(a[..i], b[..])
  {
    var prev := res;
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      res := res + [a[i]];
    }
    assert prev == IntersectSeq(a[..i], b[..]);
    assert res == IntersectSeq(a[..i+1], b[..]);
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
