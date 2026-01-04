// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.

function {:fuel 10} IntersectPrefix<T(==)>(s: seq<T>, b: seq<T>): seq<T>
{
  if |s| == 0 then
    []
  else
    var t := IntersectPrefix(s[..|s|-1], b);
    if s[|s|-1] in b && s[|s|-1] !in t then t + [s[|s|-1]] else t
}

method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == IntersectPrefix(a[..], b[..])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == IntersectPrefix(a[..i], b[..])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      res := res + [a[i]];
      assert res == IntersectPrefix(a[..i+1], b[..]);
    } else {
      assert res == IntersectPrefix(a[..i+1], b[..]);
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
