// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.

predicate NoDups<T>(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma NoDupsAppend<T>(s: seq<T>, x: T)
  requires NoDups(s)
  requires x !in s
  ensures NoDups(s + [x])
{
}

function {:fuel 50} InterSpec<T(==)>(a: seq<T>, b: seq<T>): seq<T>
{
  if |a| == 0 then []
  else
    var r := InterSpec(a[..|a|-1], b);
    if a[|a|-1] in b && a[|a|-1] !in r then r + [a[|a|-1]] else r
}

method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures NoDups(res)
  ensures res == InterSpec(a[..], b[..])
  ensures forall x :: x in res ==> x in a[..] && x in b[..]
  ensures forall x :: x in a[..] && x in b[..] ==> x in res
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant NoDups(res)
    invariant res == InterSpec(a[..i], b[..])
    invariant forall x :: x in res ==> x in a[..i] && x in b[..]
    invariant forall x :: x in a[..i] && x in b[..] ==> x in res
  {
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      NoDupsAppend(res, a[i]);
      res := res + [a[i]];
    }

    assert a[..i+1][..|a[..i+1]|-1] == a[..i];
    assert a[..i+1][|a[..i+1]|-1] == a[i];
    assert InterSpec(a[..i+1], b[..]) ==
      (if a[i] in b[..] && a[i] !in InterSpec(a[..i], b[..]) then InterSpec(a[..i], b[..]) + [a[i]] else InterSpec(a[..i], b[..]));
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
