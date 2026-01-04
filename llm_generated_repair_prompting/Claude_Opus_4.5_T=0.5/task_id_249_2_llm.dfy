// Ghost function to compute intersection preserving order from first sequence
ghost function seqIntersect<T(==)>(s1: seq<T>, s2: seq<T>): seq<T>
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
  ensures forall x :: x in res ==> x in a[..] && x in b[..]
  ensures forall x :: x in a[..] && x in b[..] ==> x in res
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < |res| ==> exists j :: 0 <= j < a.Length && a[j] == res[i]
  ensures res == seqIntersect(a[..], b[..])
{
  res := [];
  for i := 0 to a.Length
    invariant forall x :: x in res ==> x in a[..i] && x in b[..]
    invariant forall x :: x in a[..i] && x in b[..] ==> x in res
    invariant forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
    invariant forall j :: 0 <= j < |res| ==> exists k :: 0 <= k < i && a[k] == res[j]
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

  assert a[..] == [1, 2, 3];
  assert b[..] == [1, 3, 1];
  assert c[..] == [2, 4, 6];

  // Typical case
  var res1 := Intersection(a, b);
  assert seqIntersect([1, 2, 3], [1, 3, 1]) == [1, 3];
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert seqIntersect([1, 3, 1], [2, 4, 6]) == [];
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert seqIntersect([1, 3, 1], [1, 2, 3]) == [1, 3];
  assert res3 == [1, 3] || res3 == [3, 1];
}

