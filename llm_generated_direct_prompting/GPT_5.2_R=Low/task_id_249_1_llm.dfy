predicate NoDup<T>(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate IsSubseq<T(==)>(s: seq<T>, t: seq<T>)
  decreases |s|
{
  if |s| == 0 then true
  else exists k :: 0 <= k < |t| && t[k] == s[|s|-1] && IsSubseq(s[..|s|-1], t[..k])
}

lemma SubseqAppendLast<T(==)>(s: seq<T>, t: seq<T>, x: T)
  requires IsSubseq(s, t)
  ensures IsSubseq(s + [x], t + [x])
{
}

lemma SubseqAppendRight<T(==)>(s: seq<T>, t: seq<T>, x: T)
  requires IsSubseq(s, t)
  ensures IsSubseq(s, t + [x])
{
}

// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures NoDup(res)
  ensures IsSubseq(res, a[..])
  ensures forall x :: x in res ==> x in a[..] && x in b[..]
  ensures forall x :: x in a[..] && x in b[..] ==> x in res
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant NoDup(res)
    invariant IsSubseq(res, a[..i])
    invariant forall x :: x in res ==> x in a[..i] && x in b[..]
    invariant forall x :: x in a[..i] && x in b[..] ==> x in res
  {
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      assert a[..i+1] == a[..i] + [a[i]];
      SubseqAppendLast(res, a[..i], a[i]);
      res := res + [a[i]];
    } else {
      SubseqAppendRight(res, a[..i], a[i]);
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
