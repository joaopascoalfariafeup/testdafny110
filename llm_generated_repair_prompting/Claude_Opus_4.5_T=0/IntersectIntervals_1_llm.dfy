// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).

ghost function IntersectAll(s: seq<(real, real)>): (real, real)
    requires |s| >= 1
{
    if |s| == 1 then s[0]
    else intersect(IntersectAll(s[..|s|-1]), s[|s|-1])
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
        invariant r.0 < r.1
    {
        assert a[..i+1] == a[..i] + [a[i]];
        r := intersect(r, a[i]);
        if r.0 >= r.1 {
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
    assert IntersectAll(a1[..]) == (2.0, 3.0);
    assert r1 == (2.0, 3.0);

    // Disjoint intervals
    var a2 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    var r2 := IntersectIntervals(a2);
    assert a2[..] == [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    assert IntersectAll(a2[..]).0 >= IntersectAll(a2[..]).1;
    assert r2 == (0.0, 0.0);
}
