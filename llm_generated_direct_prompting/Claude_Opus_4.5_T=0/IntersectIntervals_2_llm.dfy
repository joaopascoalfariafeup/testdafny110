// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).

ghost function IntersectAll(a: seq<(real, real)>): (real, real)
    requires |a| >= 1
{
    if |a| == 1 then a[0]
    else intersect(IntersectAll(a[..|a|-1]), a[|a|-1])
}

method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
    requires a.Length >= 1
    requires forall k :: 0 <= k < a.Length ==> a[k].0 < a[k].1
    ensures var full := IntersectAll(a[..]); 
            if full.0 >= full.1 then r == (0.0, 0.0) else r == full
{
    r := a[0];
    for i := 1 to a.Length 
        invariant r == IntersectAll(a[..i])
    {
        r := intersect(r, a[i]);
        assert a[..i+1] == a[..i] + [a[i]];
        if r.0 >= r.1 {
            assert IntersectAll(a[..i+1]).0 >= IntersectAll(a[..i+1]).1;
            IntersectAllMonotonic(a[..], i+1);
            return (0.0, 0.0);
        }
    }
    assert a[..a.Length] == a[..];
}

// Computes the intersection of two intervals
function intersect(i: (real, real), j :(real, real)): (real, real)  {
    (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1)
}

lemma IntersectAllMonotonic(a: seq<(real, real)>, k: int)
    requires 1 <= k <= |a|
    requires IntersectAll(a[..k]).0 >= IntersectAll(a[..k]).1
    ensures IntersectAll(a).0 >= IntersectAll(a).1
{
    if k == |a| {
        assert a[..k] == a;
    } else {
        var prev := IntersectAll(a[..k]);
        assert a[..k+1] == a[..k] + [a[k]];
        var next := intersect(prev, a[k]);
        assert next.0 >= prev.0;
        assert next.1 <= prev.1;
        assert next.0 >= next.1;
        assert IntersectAll(a[..k+1]) == next;
        IntersectAllMonotonic(a, k+1);
    }
}

method {:fuel IntersectAll, 3} TestIntersectIntervals()
{
    // Overlaping intervals
    var a1 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
    var r1 := IntersectIntervals(a1);
    assert a1[..] == [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
    assert r1 == (2.0, 3.0);

    // Disjoint intervals
    var a2 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    var r2 := IntersectIntervals(a2);
    assert a2[..] == [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    assert r2 == (0.0, 0.0);
}
