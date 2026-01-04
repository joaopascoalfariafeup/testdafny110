// A sequence comprehension for "take first occurrences from a, filtered by membership in b"
// (used to express the ordering property precisely).
ghost function SeqIntersection<T>(sa: seq<T>, sb: seq<T>): seq<T>
  decreases |sa|
{
  if |sa| == 0 then []
  else
    var x := sa[0];
    var tail := sa[1..];
    if x in sb && x !in tail && x !in SeqIntersection(tail, sb) then [x] + SeqIntersection(tail, sb)
    else SeqIntersection(tail, sb)
}

// Helper lemma to update SeqIntersection when extending the prefix by one element
lemma SeqIntersectionExtend<T>(s: seq<T>, sb: seq<T>)
  ensures SeqIntersection(s + [s[|s|-1]], sb) ==
          (if s[|s|-1] in sb && s[|s|-1] !in s && s[|s|-1] !in SeqIntersection(s, sb)
           then SeqIntersection(s, sb) + [s[|s|-1]]
           else SeqIntersection(s, sb))
{
  // Let last := s[|s|-1]. We prove the equality by unfolding on the front of (s+[last]),
  // which is the same as unfolding on s's front repeatedly.
  // Dafny can complete this by induction on |s|.
  if |s| == 0 {
  } else {
    SeqIntersectionExtend(s[1..], sb);
  }
}

// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures forall x: T :: x in res <==> (x in a[..] && x in b[..])
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures res == SeqIntersection(a[..], b[..])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall x: T :: x in res ==> x in b[..]
    invariant forall x: T :: x in res ==> x in a[..i]
    // We only need the ==> direction for membership; the reverse direction is not true
    // when a[..i] contains duplicates (res keeps only first occurrences).
    invariant forall x: T :: x in SeqIntersection(a[..i], b[..]) ==> x in res
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
    invariant res == SeqIntersection(a[..i], b[..])
  {
    // Help Dafny relate a[..i+1] to a[..i] and [a[i]]
    assert a[..i+1] == a[..i] + [a[i]];

    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      // Use the characterization of SeqIntersection when extending the prefix by a[i]
      SeqIntersectionExtend(a[..i], b[..]);

      // Maintain the main invariant after appending a[i]
      res := res + [a[i]];
    } else {
      // Still, SeqIntersection may or may not add a[i]; show it doesn't when we don't.
      SeqIntersectionExtend(a[..i], b[..]);
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

