
// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence among those duplicates 
// (this holds from a specification perspective; the implementation may choose to follow a more specific policy).

ghost predicate NoDuplicates<T(==)>(s: seq<T>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

ghost predicate AllInBoth<T(==)>(s: seq<T>, a: seq<T>, b: seq<T>) {
  forall x :: x in s ==> x in a && x in b
}

ghost predicate AllCommonIn<T(==)>(s: seq<T>, a: seq<T>, b: seq<T>) {
  forall x :: x in a && x in b ==> x in s
}

ghost function {:fuel 5} seqIntersection<T(==)>(a: seq<T>, b: seq<T>): seq<T>
{
  seqIntersectionHelper(a, b, [])
}

ghost function {:fuel 5} seqIntersectionHelper<T(==)>(a: seq<T>, b: seq<T>, acc: seq<T>): seq<T>
{
  if a == [] then acc
  else if a[0] in b && a[0] !in acc then seqIntersectionHelper(a[1..], b, acc + [a[0]])
  else seqIntersectionHelper(a[1..], b, acc)
}

method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures NoDuplicates(res)
  ensures AllInBoth(res, a[..], b[..])
  ensures AllCommonIn(res, a[..], b[..])
  ensures forall x :: x in res ==> x in a[..] && x in b[..]
  ensures res == seqIntersection(a[..], b[..])
{
  res := [];
  for i := 0 to a.Length
    invariant NoDuplicates(res)
    invariant forall x :: x in res ==> x in a[..i] && x in b[..]
    invariant forall j :: 0 <= j < i ==> (a[j] in b[..] ==> a[j] in res)
    invariant res == seqIntersectionHelper(a[i..], b[..], res)
  {
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      res := res + [a[i]];
    }
  }
  assert a[..] == a[..a.Length];
}

// Test cases checked statically
method IntersectionTest(){
  var a := new int[] [1, 2, 3];
  var b := new int[] [1, 3, 1];
  var c := new int[] [2, 4, 6];

  // Typical case
  var res1 := Intersection(a, b);
  assert a[..] == [1, 2, 3];
  assert b[..] == [1, 3, 1];
  assert 1 in a[..] && 1 in b[..];
  assert 3 in a[..] && 3 in b[..];
  assert 2 in a[..] && 2 !in b[..];
  assert forall x :: x in a[..] && x in b[..] ==> x == 1 || x == 3;
  assert 1 in res1 && 3 in res1;
  // Helper assertions for seqIntersection computation
  assert seqIntersectionHelper([1, 2, 3], [1, 3, 1], []) == seqIntersectionHelper([2, 3], [1, 3, 1], [1]);
  assert seqIntersectionHelper([2, 3], [1, 3, 1], [1]) == seqIntersectionHelper([3], [1, 3, 1], [1]);
  assert seqIntersectionHelper([3], [1, 3, 1], [1]) == seqIntersectionHelper([], [1, 3, 1], [1, 3]);
  assert seqIntersectionHelper([], [1, 3, 1], [1, 3]) == [1, 3];
  assert seqIntersection([1, 2, 3], [1, 3, 1]) == [1, 3];
  assert |res1| == 2;
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert b[..] == [1, 3, 1];
  assert c[..] == [2, 4, 6];
  assert forall x :: x in b[..] ==> x !in c[..];
  // Helper assertions for seqIntersection computation
  assert seqIntersectionHelper([1, 3, 1], [2, 4, 6], []) == seqIntersectionHelper([3, 1], [2, 4, 6], []);
  assert seqIntersectionHelper([3, 1], [2, 4, 6], []) == seqIntersectionHelper([1], [2, 4, 6], []);
  assert seqIntersectionHelper([1], [2, 4, 6], []) == seqIntersectionHelper([], [2, 4, 6], []);
  assert seqIntersectionHelper([], [2, 4, 6], []) == [];
  assert seqIntersection([1, 3, 1], [2, 4, 6]) == [];
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert b[..] == [1, 3, 1];
  assert a[..] == [1, 2, 3];
  assert 1 in res3 && 3 in res3;
  // Helper assertions for seqIntersection computation
  assert seqIntersectionHelper([1, 3, 1], [1, 2, 3], []) == seqIntersectionHelper([3, 1], [1, 2, 3], [1]);
  assert seqIntersectionHelper([3, 1], [1, 2, 3], [1]) == seqIntersectionHelper([1], [1, 2, 3], [1, 3]);
  assert seqIntersectionHelper([1], [1, 2, 3], [1, 3]) == seqIntersectionHelper([], [1, 2, 3], [1, 3]);
  assert seqIntersectionHelper([], [1, 2, 3], [1, 3]) == [1, 3];
  assert seqIntersection([1, 3, 1], [1, 2, 3]) == [1, 3];
  assert |res3| == 2;
  assert res3 == [1, 3] || res3 == [3, 1];
  //@invalid assert res3 == [1, 3]; // not guaranteed
  //@invalid assert res3 == [3, 1]; // not guaranteed
}

