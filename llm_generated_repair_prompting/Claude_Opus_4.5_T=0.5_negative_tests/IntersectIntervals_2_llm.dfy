// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).

ghost function {:fuel 4} IntersectAll(a: seq<(real, real)>): (real, real)
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else intersect(IntersectAll(a[..|a|-1]), a[|a|-1])
}

predicate ValidInterval(i: (real, real)) {
    i.0 < i.1
}

predicate AllValidIntervals(a: seq<(real, real)>) {
    forall k :: 0 <= k < |a| ==> ValidInterval(a[k])
}

// Lemma: if intersection at position i is empty, then intersection of full array is also empty
lemma IntersectAllMonotonic(a: seq<(real, real)>, i: int)
    requires 0 < i <= |a|
    requires IntersectAll(a[..i]).0 >= IntersectAll(a[..i]).1
    ensures IntersectAll(a[..]).0 >= IntersectAll(a[..]).1
    decreases |a| - i
{
    if i == |a| {
        assert a[..i] == a[..];
    } else {
        var curr := IntersectAll(a[..i]);
        assert a[..i+1] == a[..i] + [a[i]];
        var next := intersect(curr, a[i]);
        // If curr.0 >= curr.1, then next.0 >= next.1 or next remains invalid
        assert next.0 >= next.1;
        IntersectAllMonotonic(a, i + 1);
    }
}

method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
    requires a.Length > 0
    requires AllValidIntervals(a[..])
    ensures var intersection := IntersectAll(a[..]);
            if intersection.0 < intersection.1 then r == intersection
            else r == (0.0, 0.0)
{
    r := a[0];
    for i := 1 to a.Length 
        invariant r == IntersectAll(a[..i])
    {
        assert a[..i+1] == a[..i] + [a[i]];
        r := intersect(r, a[i]);
        if r.0 >= r.1 {
            IntersectAllMonotonic(a[..], i + 1);
            return (0.0, 0.0);
        }
    }
    assert a[..a.Length] == a[..];
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
    assert a1[..] == [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
    assert a1[..1] == [(0.0, 3.0)];
    assert a1[..2] == [(0.0, 3.0), (1.0, 4.0)];
    assert IntersectAll(a1[..1]) == (0.0, 3.0);
    assert IntersectAll(a1[..2]) == (1.0, 3.0);
    assert IntersectAll(a1[..]) == (2.0, 3.0);
    assert r1 == (2.0, 3.0);

    // Disjoint intervals
    var a2 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    var r2 := IntersectIntervals(a2);
    assert a2[..] == [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    assert a2[..1] == [(0.0, 3.0)];
    assert a2[..2] == [(0.0, 3.0), (1.0, 4.0)];
    assert IntersectAll(a2[..1]) == (0.0, 3.0);
    assert IntersectAll(a2[..2]) == (1.0, 3.0);
    assert IntersectAll(a2[..]) == (3.0, 3.0);
    assert r2 == (0.0, 0.0);

    var a3 := new (real, real)[] [(0.0, 0.0), (0.0, 1.0)];
    //@invalid var r3 := IntersectIntervals(a3); should not verify due to precondition violation
}
