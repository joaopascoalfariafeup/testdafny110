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
// NOTE: SeqIntersection scans from the front and keeps the *last* occurrence of a value in sa.
// When appending x at the end, any earlier occurrence of x will be dropped.
lemma SeqIntersectionExtend<T>(s: seq<T>, x: T, sb: seq<T>)
  ensures SeqIntersection(s + [x], sb) ==
          (if x in sb
           then SeqIntersection(s, sb) + [x]
           else SeqIntersection(s, sb))
{
  // Proof by unfolding SeqIntersection on (s + [x]) from the front.
  if |s| == 0 {
    // SeqIntersection([x], sb) is [x] iff x in sb else []
  } else {
    var h := s[0];
    var t := s[1..];

    // Establish the useful identities about tails
    assert (s + [x])[0] == h;
    assert (s + [x])[1..] == t + [x];

    // Induction on the tail
    SeqIntersectionExtend(t, x, sb);

    // Now unfold SeqIntersection(s + [x], sb) and SeqIntersection(s, sb)
    // Case split follows SeqIntersection's definition on head h.
    if h in sb && h !in (t + [x]) {
      // Since h !in (t + [x]), in particular h !in t and h != x
      assert h !in t;
      assert h != x;

      // So SeqIntersection(s + [x], sb) = [h] + SeqIntersection(t + [x], sb)
      // and SeqIntersection(s, sb)      = [h] + SeqIntersection(t, sb)
      // Use IH on SeqIntersection(t + [x], sb) and reassociate.
      if x in sb {
        calc {
          SeqIntersection(s + [x], sb);
          == [h] + SeqIntersection(t + [x], sb);
          == [h] + (SeqIntersection(t, sb) + [x]);
          == ([h] + SeqIntersection(t, sb)) + [x];
          == SeqIntersection(s, sb) + [x];
        }
      } else {
        calc {
          SeqIntersection(s + [x], sb);
          == [h] + SeqIntersection(t + [x], sb);
          == [h] + SeqIntersection(t, sb);
          == SeqIntersection(s, sb);
        }
      }
    } else {
      // Either h !in sb or h in (t + [x]); in both cases head h is not kept.
      // So SeqIntersection(s + [x], sb) = SeqIntersection(t + [x], sb).
      if x in sb {
        calc {
          SeqIntersection(s + [x], sb);
          == SeqIntersection(t + [x], sb);
          == SeqIntersection(t, sb) + [x];
          == SeqIntersection(s, sb) + [x];
        }
      } else {
        calc {
          SeqIntersection(s + [x], sb);
          == SeqIntersection(t + [x], sb);
          == SeqIntersection(t, sb);
          == SeqIntersection(s, sb);
        }
      }
    }
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
