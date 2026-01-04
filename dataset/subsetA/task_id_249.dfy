// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence among those duplicates 
// (this holds from a specification perspective; the implementation may choose to follow a more specific policy).
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..] && res[k] in b[..]
  ensures forall x :: x in a[..] && x in b[..] ==> x in res
  ensures forall p,q :: 0 <= p < q < |res| ==> res[p] != res[q]
  ensures forall p,q :: 0 <= p < q < |res| ==> exists i, j :: 0 <= i < j < a.Length && a[i] == res[p] && a[j] == res[q]
{
  res := [];
  for i := 0 to a.Length
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i] && res[k] in b[..]
    invariant forall p,q :: 0 <= p < q < |res| ==> res[p] != res[q]
    invariant forall x :: x in a[..i] && x in b[..] ==> x in res
    invariant forall p,q :: 0 <= p < q < |res| ==> exists r,s :: 0 <= r < s < i && a[r] == res[p] && a[s] == res[q]
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
  assert a[..] == [1, 2, 3]; // helper
  assert b[..] == [1, 3, 1];  // helper
  assert c[..] == [2, 4, 6]; // helper

  // Typical case
  var res1 := Intersection(a, b);
  assert 1 in res1 && 3 in res1; // helper
  assert |res1| > 2 ==> res1[2] == res1[0] || res1[2] == res1[1]; // helper by contradiction
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert |res2| > 0 ==> res2[0] in b[..] && res2[0] in c[..]; // helper by contradiction
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert 1 in res3 && 3 in res3; // helper
  assert |res3| > 2 ==> res3[2] == res3[0] || res3[2] == res3[1]; // helper by contradiction
  assert res3 == [1, 3] || res3 == [3, 1];
  //@invalid assert res3 == [1, 3]; // not guaranteed
  //@invalid assert res3 == [3, 1]; // not guaranteed
}