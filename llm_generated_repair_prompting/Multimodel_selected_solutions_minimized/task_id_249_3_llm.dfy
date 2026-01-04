ghost function {:fuel 5} seqIntersect<T(==)>(s1: seq<T>, s2: seq<T>): seq<T>
{
  if s1 == [] then []
  else 
    var rest := seqIntersect(s1[..|s1|-1], s2);
    if s1[|s1|-1] in s2 && s1[|s1|-1] !in rest then rest + [s1[|s1|-1]]
    else rest
}

// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == seqIntersect(a[..], b[..])
{
  res := [];
  for i := 0 to a.Length
    invariant res == seqIntersect(a[..i], b[..])
  {
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      res := res + [a[i]];
    }
    assert a[..i+1] == a[..i] + [a[i]];
  }
  assert a[..a.Length] == a[..];
}

// Test cases checked statically
method IntersectionTest(){
  var a := new int[] [1, 2, 3];
  var b := new int[] [1, 3, 1];
  var c := new int[] [2, 4, 6];

  assert b[..] == [1, 3, 1];

  // Typical case
  var res1 := Intersection(a, b);
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
}