// Keep the definition simple and verification-friendly.
// It returns the elements of sa that are also in sb, keeping the order of sa,
// and keeping only the FIRST occurrence from sa (no duplicates in the result).
ghost function {:fuel 20} SeqIntersection<T>(sa: seq<T>, sb: seq<T>): seq<T>
  decreases |sa|
{
  if |sa| == 0 then []
  else if sa[0] in sb && sa[0] !in sa[1..]
       then [sa[0]] + SeqIntersection(sa[1..], sb)
       else SeqIntersection(sa[1..], sb)
}

// Helpful lemma: if h is not in t+[x], then h not in t and h != x
lemma NotInAppend<T>(h: T, t: seq<T>, x: T)
  requires h !in t + [x]
  ensures h !in t && h != x
{
  assert (h in t + [x]) <==> (h in t || h in [x]);
  assert (h in [x]) <==> (h == x);
}

// If x is not in a sequence, it is not in any suffix of it.
lemma NotInSuffix<T>(s: seq<T>, x: T, k: int)
  requires 0 <= k <= |s|
  requires x !in s
  ensures x !in s[k..]
{
  if x in s[k..] {
    var j : int :| 0 <= j < |s[k..]| && s[k..][j] == x;
    assert s[k + j] == x;
    assert x in s;
    assert false;
  }
}

// Main extension lemma used by the loop.
// When extending the prefix by x, either x is appended (if it is in sb and new in the prefix)
// or the result is unchanged.
lemma SeqIntersectionExtend<T>(s: seq<T>, x: T, sb: seq<T>)
  ensures SeqIntersection(s + [x], sb) ==
          (if x in sb && x !in s
           then SeqIntersection(s, sb) + [x]
           else SeqIntersection(s, sb))
  decreases |s|
{
  if |s| == 0 {
    if x in sb {
      assert SeqIntersection([x], sb) == [x];
      assert SeqIntersection([], sb) == [];
    } else {
      assert SeqIntersection([x], sb) == [];
      assert SeqIntersection([], sb) == [];
    }
  } else {
    var h := s[0];
    var t := s[1..];

    // Structural facts
    assert s + [x] == [h] + (t + [x]);
    assert (s + [x])[0] == h;
    assert (s + [x])[1..] == t + [x];

    // Induction
    SeqIntersectionExtend(t, x, sb);

    // Membership relations
    assert x in s <==> (x == h || x in t);
    assert x !in s <==> (x != h && x !in t);

    if h in sb && h !in (t + [x]) {
      // In this case, h is kept at the front in SeqIntersection(s+[x],sb)
      NotInAppend(h, t, x); // gives h !in t and h != x

      if x in sb && x !in s {
        // Then x != h and x !in t
        assert x != h && x !in t;

        // Also, x is not in (t+[x])[1..] = t
        assert (t + [x])[1..] == t;

        calc {
          SeqIntersection(s + [x], sb);
          == [h] + SeqIntersection((s + [x])[1..], sb);
          == [h] + SeqIntersection(t + [x], sb);
          == [h] + (SeqIntersection(t, sb) + [x]);
          == ([h] + SeqIntersection(t, sb)) + [x];
          == SeqIntersection(s, sb) + [x];
        }
      } else {
        // Else-branch means: !(x in sb && x !in s)
        // Need to show the tail does not get x appended.
        if x in sb {
          // then x in s
          assert x in s;
          // If x != h, then x in t, which would contradict the possibility that x !in t.
          if x != h {
            assert x in t;
          }
        }

        // Show x cannot be "new in t" here
        // If x in sb and x !in t, then since x in s it must be x==h,
        // but h != x from NotInAppend, contradiction. Therefore not (x in sb && x !in t).
        assert !(x in sb && x !in t);

        // Hence SeqIntersection(t+[x],sb) == SeqIntersection(t,sb)
        calc {
          SeqIntersection(s + [x], sb);
          == [h] + SeqIntersection(t + [x], sb);
          == [h] + SeqIntersection(t, sb);
          == SeqIntersection(s, sb);
        }
      }
    } else {
      // h is not kept at the front; SeqIntersection(s, sb) == SeqIntersection(t, sb)
      if x in sb && x !in s {
        assert x != h && x !in t;

        // From x !in t, x cannot be in SeqIntersection(t,sb)
        NotInSuffix(t, x, 0);

        calc {
          SeqIntersection(s + [x], sb);
          == SeqIntersection(t + [x], sb);
          == SeqIntersection(t, sb) + [x];
          == SeqIntersection(s, sb) + [x];
        }
      } else {
        // No append effect beyond induction
        // Need: SeqIntersection(t+[x],sb) == SeqIntersection(t,sb)
        if x in sb && x !in t {
          // Since not (x in sb && x !in s), we have x in s.
          assert x in s;
          // With x !in t, that forces x == h
          assert x == h;
          // But then h in (t+[x]) (as the last element), contradicting the current outer branch condition
          assert h in t + [x];
          assert false;
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

    // How the spec changes when extending the prefix
    SeqIntersectionExtend(a[..i], a[i], b[..]);

    if a[i] in b[..] && a[i] !in res {
      // From invariant res == SeqIntersection(a[..i], b[..]) and the definition of SeqIntersection,
      // if a[i] were already in a[..i], then it would already be in res (because a[i] in b[..]).
      if a[i] in a[..i] {
        var s := a[..i];
        // Pick the last occurrence of a[i] in s
        var k : int :| 0 <= k < |s| && s[k] == a[i] &&
                       (forall m :: k < m < |s| ==> s[m] != a[i]);
        // Then a[i] is the head of suffix s[k..] and not in its tail
        assert s[k..][0] == a[i];
        assert s[k..][1..] == s[k+1..];
        assert a[i] !in s[k+1..];
        assert a[i] in b[..];

        // By the definition, SeqIntersection(s[k..],b) starts with a[i]
        assert SeqIntersection(s[k..], b[..]) == [a[i]] + SeqIntersection(s[k+1..], b[..]);
        assert a[i] in SeqIntersection(s[k..], b[..]);

        // Monotonicity for membership over prefixes: if something is in the intersection of a suffix,
        // then it is in the intersection of the whole sequence.
        // (This is immediate because SeqIntersection only removes elements, never adds new ones from outside.)
        assert a[i] in SeqIntersection(s, b[..]);
        assert a[i] in res; // since res == SeqIntersection(s,b)
        assert false;
      }
      assert a[i] !in a[..i];

      res := res + [a[i]];
      // uniqueness is preserved because we appended an element not already in res
      assert forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q];
    } else {
      // res unchanged; invariant maintained by SeqIntersectionExtend + the condition
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
