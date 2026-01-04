predicate validInterval(i: (real, real)) 
{
    i.0 <= i.1
}

predicate validArray(a: array<(real, real)>) 
{
    (forall i :: 0 <= i < a.Length ==> validInterval(a[i]))
}

method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
    requires a != null && a.Length > 0 && validArray(a)
    ensures validInterval(r) && (forall i :: 0 <= i < a.Length ==> (r.0 >= a[i].0 && r.1 <= a[i].1) || (r.0 == 0.0 && r.1 == 0.0))
{
    r := a[0];
    for i := 1 to a.Length 
        invariant 1 <= i <= a.Length
        invariant validInterval(r) && (forall j :: 0 <= j < i ==> (r.0 >= a[j].0 && r.1 <= a[j].1) || (r.0 == 0.0 && r.1 == 0.0))
    {
        r := intersect(r, a[i]);
        if r.0 >= r.1 {
            return (0.0, 0.0);
        }
    }
}

function intersect(i: (real, real), j :(real, real)): (real, real)  
    requires validInterval(i) && validInterval(j)
    ensures validInterval(r) && ((r.0 >= i.0 && r.0 >= j.0 && r.1 <= i.1 && r.1 <= j.1) || (r.0 == 0.0 && r.1 == 0.0))
{
    var r := (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1);
    return r;
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

