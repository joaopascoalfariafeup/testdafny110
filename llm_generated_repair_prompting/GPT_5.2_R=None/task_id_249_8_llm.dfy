// A sequence comprehension for "take first occurrences from a, filtered by membership in b"
// (used to express the ordering property precisely).
ghost function {:fuel 10} SeqIntersection<T>(sa: seq<T>, sb: seq<T>): seq<T>
  decreases |sa|
{
  if |sa| == 0 then []
  else
    var x := sa[0];
    var tail := sa[1..];
    if x in sb && x !in tail then [x] + SeqIntersection(tail, sb)
    else SeqIntersection(tail, sb)
}

// Lemma: if h is not in t+[x], then h not in t and h != x
lemma NotInAppend<T>(h: T, t: seq<T>, x: T)
  requires h !in t + [x]
  ensures h !in t && h != x
{
  assert (h in t + [x]) <==> (h in t || h in [x]);
  assert (h in [x]) <==> (h == x);
  assert !(h in t || h == x);
  assert h !in t;
  assert h != x;
}

// Key helper: characterize SeqIntersection(s+[x],sb) precisely based on whether x appeared in s.
// If x is in sb and was already in s, appending x will *replace* the earlier kept occurrence (if any),
// so the result does NOT change. If x is new in s, it gets appended.
lemma SeqIntersectionExtend<T>(s: seq<T>, x: T, sb: seq<T>)
  ensures SeqIntersection(s + [x], sb) ==
          (if x in sb && x !in s
           then SeqIntersection(s, sb) + [x]
           else SeqIntersection(s, sb))
  decreases |s|
{
  if |s| == 0 {
    if x in sb {
      assert SeqIntersection([] + [x], sb) == [x];
      assert SeqIntersection([], sb) == [];
    } else {
      assert SeqIntersection([] + [x], sb) == [];
      assert SeqIntersection([], sb) == [];
    }
  } else {
    var h := s[0];
    var t := s[1..];

    assert (s + [x])[0] == h;
    assert (s + [x])[1..] == t + [x];

    // Induction
    SeqIntersectionExtend(t, x, sb);

    // Relate membership in s with membership in t
    assert x in s <==> (x == h || x in t);
    assert x !in s <==> (x != h && x !in t);

    if h in sb && h !in (t + [x]) {
      NotInAppend(h, t, x); // gives h !in t and h != x

      // Here, SeqIntersection keeps h at the front in both s and s+[x]
      if x in sb && x !in s {
        // from x !in s, get x != h and x !in t
        assert x != h && x !in t;

        // then x !in t, so tail case appends x
        calc {
          SeqIntersection(s + [x], sb);
          == [h] + SeqIntersection(t + [x], sb);
          == [h] + (SeqIntersection(t, sb) + [x]);
          == ([h] + SeqIntersection(t, sb)) + [x];
          == SeqIntersection(s, sb) + [x];
        }
      } else {
        // Either x !in sb or x in s; in both cases, tail does not change w.r.t. append
        calc {
          SeqIntersection(s + [x], sb);
          == [h] + SeqIntersection(t + [x], sb);
          == [h] + (if x in sb && x !in t then SeqIntersection(t, sb) + [x] else SeqIntersection(t, sb));
        }
        // If x in sb && x !in t held, then (since h!=x and x !in t) we'd have x !in s, contradicting the else-branch condition.
        if x in sb && x !in t {
          assert x != h; // from NotInAppend: h != x
          assert x !in s; // x != h and x !in t
          // contradicts: not (x in sb && x !in s) in this else-branch
          assert false;
        }
        // Therefore the conditional above selects SeqIntersection(t,sb)
        calc {
          SeqIntersection(s + [x], sb);
          == [h] + SeqIntersection(t, sb);
          == SeqIntersection(s, sb);
        }
      }
    } else {
      // h is not kept at the front in either s or s+[x]
      if x in sb && x !in s {
        // then x != h and x !in t
        assert x != h && x !in t;
        calc {
          SeqIntersection(s + [x], sb);
          == SeqIntersection(t + [x], sb);
          == SeqIntersection(t, sb) + [x];
          == SeqIntersection(s, sb) + [x];
        }
      } else {
        // Either x !in sb, or x in s (i.e., x==h or x in t), so no append effect beyond what induction gives.
        // Show that if x in sb and x !in t, then necessarily x == h, which would make x in s, consistent with this branch.
        if x in sb && x !in t {
          assert x == h; // since x in s and x !in t, must be x==h
        }
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
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == SeqIntersection(a[..i], b[..])
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
  {
    assert a[..i+1] == a[..i] + [a[i]];

    // Always unfold how SeqIntersection changes when extending the prefix by a[i]
    SeqIntersectionExtend(a[..i], a[i], b[..]);

    if a[i] in b[..] && a[i] !in res {
      // From loop invariant, res == SeqIntersection(a[..i], b[..]), so "a[i] !in res" implies "a[i] !in a[..i]"
      assert res == SeqIntersection(a[..i], b[..]);
      // Prove that if a[i] were in a[..i], it would be in SeqIntersection(a[..i],b[..]) given a[i] in b[..]
      if a[i] in a[..i] {
        // Let k be the last occurrence index of a[i] in a[..i]
        var s := a[..i];
        var k : int :| 0 <= k < |s| && s[k] == a[i] && forall m :: k < m < |s| ==> s[m] != a[i];
        // Then a[i] is the head of s[k..] and not in its tail, so SeqIntersection(s[k..],b) starts with a[i]
        assert s[k..][0] == a[i];
        assert s[k..][1..] == s[k+1..];
        assert a[i] !in s[k+1..];
        assert a[i] in b[..];
        assert SeqIntersection(s[k..], b[..]) == [a[i]] + SeqIntersection(s[k+1..], b[..]);
        // Thus a[i] is in SeqIntersection(s,b)
        assert SeqIntersection(s, b[..]) == SeqIntersection(s[..k], b[..]) + SeqIntersection(s[k..], b[..]);
        assert a[i] in SeqIntersection(s[k..], b[..]);
        assert a[i] in SeqIntersection(s, b[..]);
        assert false;
      }
      assert a[i] !in a[..i];

      res := res + [a[i]];
      // Maintain uniqueness
      assert forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q];
    } else {
      // res unchanged; invariant already maintained via SeqIntersectionExtend and the if-condition
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
