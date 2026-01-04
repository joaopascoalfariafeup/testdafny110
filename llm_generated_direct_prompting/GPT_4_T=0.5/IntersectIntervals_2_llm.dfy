// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).
method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
  requires a.Length > 0
  ensures forall k :: 0 <= k < a.Length ==> a[k].0 <= a[k].1
  ensures (forall k :: 0 <= k < a.Length ==> r.0 <= a[k].1 && a[k].0 <= r.1) || r == (0.0, 0.0)
{
    r := a[0];
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant (forall k :: 0 <= k < i ==> r.0 <= a[k].1 && a[k].0 <= r.1) || r == (0.0, 0.0)
    {
        r := intersect(r, a[i]);
        if r.0 >= r.1 {
            return (0.0, 0.0);
        }
    }
}

// Computes the intersection of two intervals
function intersect(i: (real, real), j :(real, real)): (real, real)  
  requires i.0 <= i.1 && j.0 <= j.1
  ensures (i.0 <= j.1 && j.0 <= i.1) ==> (res.0 <= res.1 && res.0 <= i.1 && i.0 <= res.1 && res.0 <= j.1 && j.0 <= res.1)
  ensures !(i.0 <= j.1 && j.0 <= i.1) ==> res == (0.0, 0.0)
{
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
