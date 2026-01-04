// Computes the intersection of two intervals
function intersect(i: (real, real), j: (real, real)): (real, real)  {
  (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1)
}

// Intersection of a sequence of intervals (defined for all sequences; callers here use non-empty prefixes)
ghost function {:fuel 5} IntersectSeq(s: seq<(real, real)>): (real, real)
  decreases |s|
{
  if |s| == 0 then (0.0, 0.0)
  else if |s| == 1 then s[0]
  else intersect(IntersectSeq(s[..|s|-1]), s[|s|-1])
}

lemma IntersectSeqAppendOne(s: seq<(real, real)>, x: (real, real))
  requires |s| > 0
  ensures IntersectSeq(s + [x]) == intersect(IntersectSeq(s), x)
{
  assert |s + [x]| == |s| + 1;
  assert |s + [x]| > 1;
  assert |s + [x]| - 1 == |s|;
  assert (s + [x])[..|s|] == s;
  assert (s + [x])[|s|] == x;

  calc {
    IntersectSeq(s + [x]);
    == intersect(IntersectSeq((s + [x])[..(|s + [x]| - 1)]), (s + [x])[|s + [x]| - 1]);
    == intersect(IntersectSeq(s), x);
  }
}

lemma IntersectPreservesEmpty(i: (real, real), j: (real, real))
  requires i.0 >= i.1
  ensures intersect(i, j).0 >= intersect(i, j).1
{
  var a := intersect(i, j).0;
  var b := intersect(i, j).1;

  // a = max(i.0, j.0)  => a >= i.0
  if i.0 > j.0 {
    assert a == i.0;
    assert a >= i.0;
  } else {
    assert a == j.0;
    assert i.0 <= j.0;
    assert a >= i.0;
  }

  // b = min(i.1, j.1)  => i.1 >= b
  if i.1 < j.1 {
    assert b == i.1;
    assert i.1 >= b;
  } else {
    assert b == j.1;
    assert i.1 >= j.1;
    assert i.1 >= b;
  }

  // Chain: a >= i.0 >= i.1 >= b
  assert a >= i.0;
  assert i.0 >= i.1;
  assert i.1 >= b;
  assert a >= b;
}

lemma IntersectSeqPrefixEmptyImpliesFullEmpty(s: seq<(real, real)>, n: int)
  requires 1 <= n <= |s|
  requires IntersectSeq(s[..n]).0 >= IntersectSeq(s[..n]).1
  ensures IntersectSeq(s).0 >= IntersectSeq(s).1
  decreases |s| - n
{
  if n == |s| {
    // Prefix is the whole sequence
    assert s[..n] == s;
    assert IntersectSeq(s[..n]) == IntersectSeq(s);
  } else {
    assert 0 <= n < |s|;
    assert s[..(n+1)] == s[..n] + [s[n]];

    IntersectSeqAppendOne(s[..n], s[n]);
    assert IntersectSeq(s[..(n+1)]) == intersect(IntersectSeq(s[..n]), s[n]);

    IntersectPreservesEmpty(IntersectSeq(s[..n]), s[n]);
    assert IntersectSeq(s[..(n+1)]).0 >= IntersectSeq(s[..(n+1)]).1;

    IntersectSeqPrefixEmptyImpliesFullEmpty(s, n + 1);
  }
}

// Compute the intersection of a non-empty array of non-empty closed intervals.
// If the intersection is empty, by convention returns (0.0, 0.0).
method IntersectIntervals(a: array<(real, real)>) returns (r: (real, real))
  requires a.Length > 0
  requires forall k :: 0 <= k < a.Length ==> a[k].0 < a[k].1
  ensures r != (0.0, 0.0) ==> r == IntersectSeq(a[..]) && r.0 < r.1
  ensures r == (0.0, 0.0) ==> IntersectSeq(a[..]).0 >= IntersectSeq(a[..]).1
{
  r := a[0];
  assert a[..1] == [a[0]];
  assert IntersectSeq(a[..1]) == a[0];

  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant r == IntersectSeq(a[..i])
    invariant r.0 < r.1
  {
    r := intersect(r, a[i]);

    // Relate IntersectSeq(a[..i+1]) to IntersectSeq(a[..i])
    IntersectSeqAppendOne(a[..i], a[i]);
    assert a[..i] + [a[i]] == a[..i+1];
    assert IntersectSeq(a[..i+1]) == intersect(IntersectSeq(a[..i]), a[i]);

    assert r == IntersectSeq(a[..i+1]);
    if r.0 >= r.1 {
      // If a prefix intersection is empty, the full intersection is empty too
      IntersectSeqPrefixEmptyImpliesFullEmpty(a[..], i + 1);
      return (0.0, 0.0);
    }
    assert r.0 < r.1;
  }

  // Help the verifier connect a[..a.Length] with a[..]
  assert a[..a.Length] == a[..];
}

method TestIntersectIntervals()
{
  // Overlaping intervals
  var a1 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
  var r1 := IntersectIntervals(a1);
  assert r1 == (2.0, 3.0);

  // Disjoint intervals
  var a2 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
  var r2 := IntersectIntervals(a2);
  assert r2 == (0.0, 0.0);
}
