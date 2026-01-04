// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).

ghost function {:fuel 3} IntersectAll(s: seq<(real, real)>): (real, real)
    requires |s| >= 1
{
    if |s| == 1 then s[0]
    else intersect(IntersectAll(s[..|s|-1]), s[|s|-1])
}

// Computes the intersection of two intervals
function intersect(i: (real, real), j :(real, real)): (real, real)  {
    (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1)
}

// Lemma: if intersection at position i is empty, extending the sequence keeps it empty
lemma IntersectAllEmptyExtend(s: seq<(real, real)>, i: int)
    requires 1 <= i < |s|
    requires IntersectAll(s[..i]).0 >= IntersectAll(s[..i]).1
    ensures IntersectAll(s[..i+1]).0 >= IntersectAll(s[..i+1]).1
{
    assert s[..i+1] == s[..i] + [s[i]];
    var prev := IntersectAll(s[..i]);
    var curr := intersect(prev, s[i]);
    // If prev.0 >= prev.1, then curr.0 >= curr.1
    // Because curr.0 = max(prev.0, s[i].0) >= prev.0 >= prev.1 >= min(prev.1, s[i].1) = curr.1
    // Actually: curr.0 >= prev.0 and curr.1 <= prev.1, so curr.0 >= prev.0 >= prev.1 >= curr.1
}

lemma IntersectAllEmptyPropagates(s: seq<(real, real)>, i: int)
    requires 1 <= i <= |s|
    requires IntersectAll(s[..i]).0 >= IntersectAll(s[..i]).1
    ensures IntersectAll(s).0 >= IntersectAll(s).1
    decreases |s| - i
{
    if i == |s| {
        assert s[..i] == s;
    } else {
        IntersectAllEmptyExtend(s, i);
        IntersectAllEmptyPropagates(s, i + 1);
    }
}

method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
    requires a.Length >= 1
    requires forall i :: 0 <= i < a.Length ==> a[i].0 < a[i].1
    ensures r == (0.0, 0.0) || r == IntersectAll(a[..])
    ensures r != (0.0, 0.0) ==> r.0 < r.1
    ensures r == (0.0, 0.0) ==> IntersectAll(a[..]).0 >= IntersectAll(a[..]).1
{
    r := a[0];
    for i := 1 to a.Length 
        invariant r == IntersectAll(a[..i])
    {
        assert a[..i+1] == a[..i] + [a[i]];
        r := intersect(r, a[i]);
        if r.0 >= r.1 {
            assert r == IntersectAll(a[..i+1]);
            assert IntersectAll(a[..i+1]).0 >= IntersectAll(a[..i+1]).1;
            IntersectAllEmptyPropagates(a[..], i + 1);
            return (0.0, 0.0);
        }
    }
    assert a[..a.Length] == a[..];
}

method TestIntersectIntervals()
{
    // Overlaping intervals
    var a1 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
    var r1 := IntersectIntervals(a1);
    assert a1[..] == [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
    assert IntersectAll(a1[..]) == (2.0, 3.0);
    assert r1 == (2.0, 3.0);

    // Disjoint intervals
    var a2 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    var r2 := IntersectIntervals(a2);
    assert a2[..] == [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    assert IntersectAll(a2[..]).0 >= IntersectAll(a2[..]).1;
    assert r2 == (0.0, 0.0);
}
