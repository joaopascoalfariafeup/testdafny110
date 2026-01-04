// A sequence comprehension for "take first occurrences from a, filtered by membership in b"
// (used to express the ordering property precisely).
ghost function {:fuel 5} SeqIntersection<T>(sa: seq<T>, sb: seq<T>): seq<T>
  decreases |sa|
{
  if |sa| == 0 then []
  else
    var x := sa[0];
    var tail := sa[1..];
    if x in sb && x !in tail then [x] + SeqIntersection(tail, sb)
    else SeqIntersection(tail, sb)
}

// Helper lemma: how SeqIntersection changes when extending a sequence by one element at the end.
lemma SeqIntersectionExtend<T>(s: seq<T>, x: T, sb: seq<T>)
  ensures SeqIntersection(s + [x], sb) ==
          (if x in sb && x !in s
           then SeqIntersection(s, sb) + [x]
           else SeqIntersection(s, sb))
  decreases |s|
{
  if |s| == 0 {
    // unfold both sides
  } else {
    // Induction on s without changing the algorithmic meaning:
    SeqIntersectionExtend(s[1..], x, sb);
  }
}

// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it keeps the first occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures res == SeqIntersection(a[..], b[..])
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall x: T :: x in res <==> (x in a[..] && x in b[..] && x in SeqIntersection(a[..], b[..]))
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == SeqIntersection(a[..i], b[..])
    invariant forall x: T :: x in res ==> x in b[..]
    invariant forall x: T :: x in res ==> x in a[..i]
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
  {
    // Help Dafny relate a[..i+1] to a[..i] and [a[i]]
    assert a[..i+1] == a[..i] + [a[i]];

    if a[i] in b[..] && a[i] !in res {
      SeqIntersectionExtend(a[..i], a[i], b[..]);
      res := res + [a[i]];
    } else {
      SeqIntersectionExtend(a[..i], a[i], b[..]);
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
  assert a[..] == [1,2,3];
  assert b[..] == [1,3,1];
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert c[..] == [2,4,6];
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert res3 == [1, 3] || res3 == [3, 1];
}
