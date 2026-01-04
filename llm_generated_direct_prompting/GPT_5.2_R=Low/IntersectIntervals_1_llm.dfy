// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).

ghost function MaxLower(s: seq<(real, real)>): real
  requires |s| >= 1
{
  if |s| == 1 then s[0].0
  else
    var m := MaxLower(s[..|s|-1]);
    if m > s[|s|-1].0 then m else s[|s|-1].0
}

ghost function MinUpper(s: seq<(real, real)>): real
  requires |s| >= 1
{
  if |s| == 1 then s[0].1
  else
    var m := MinUpper(s[..|s|-1]);
    if m < s[|s|-1].1 then m else s[|s|-1].1
}

ghost function InterAll(s: seq<(real, real)>): (real, real)
  requires |s| >= 1
{
  if MaxLower(s) < MinUpper(s) then (MaxLower(s), MinUpper(s)) else (0.0, 0.0)
}

lemma ExtendMonotoneMaxLower(s: seq<(real, real)>, x: (real, real))
  requires |s| >= 1
  ensures MaxLower(s + [x]) >= MaxLower(s)
{
}

lemma ExtendMonotoneMinUpper(s: seq<(real, real)>, x: (real, real))
  requires |s| >= 1
  ensures MinUpper(s + [x]) <= MinUpper(s)
{
}

lemma PrefixEmptyImpliesAllEmpty(s: seq<(real, real)>, t: seq<(real, real)>)
  requires |s| >= 1
  requires |t| >= 1
  requires s <= t
  requires MaxLower(s) >= MinUpper(s)
  ensures MaxLower(t) >= MinUpper(t)
{
  if |s| == |t| {
  } else {
    var x := t[|s|];
    var s1 := s + [x];
    assert s1 <= t;
    ExtendMonotoneMaxLower(s, x);
    ExtendMonotoneMinUpper(s, x);
    assert MaxLower(s1) >= MaxLower(s);
    assert MinUpper(s1) <= MinUpper(s);
    assert MaxLower(s1) >= MinUpper(s1);
    PrefixEmptyImpliesAllEmpty(s1, t);
  }
}

method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
  requires a.Length >= 1
  requires forall k :: 0 <= k < a.Length ==> a[k].0 < a[k].1
  ensures r == InterAll(a[..])
{
    r := a[0];
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant r.0 == MaxLower(a[..i])
      invariant r.1 == MinUpper(a[..i])
      invariant r.0 < r.1
    {
        r := intersect(r, a[i]);
        assert r.0 == (if MaxLower(a[..i]) > a[i].0 then MaxLower(a[..i]) else a[i].0);
        assert r.1 == (if MinUpper(a[..i]) < a[i].1 then MinUpper(a[..i]) else a[i].1);
        assert MaxLower(a[..i+1]) == (if MaxLower(a[..i]) > a[i].0 then MaxLower(a[..i]) else a[i].0);
        assert MinUpper(a[..i+1]) == (if MinUpper(a[..i]) < a[i].1 then MinUpper(a[..i]) else a[i].1);
        if r.0 >= r.1 {
            assert MaxLower(a[..i+1]) >= MinUpper(a[..i+1]);
            PrefixEmptyImpliesAllEmpty(a[..i+1], a[..]);
            assert MaxLower(a[..]) >= MinUpper(a[..]);
            return (0.0, 0.0);
        }
    }
}

// Computes the intersection of two intervals
function intersect(i: (real, real), j :(real, real)): (real, real)  {
    (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1)
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
