// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).
method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
  requires a.Length > 0 
  requires forall i :: 0 <= i < a.Length ==> a[i].0 < a[i].1  
  ensures var r' := MaxMin(a); if r'.0 < r'.1 then r == r' else r == (0.0, 0.0)
{
    r := a[0];
    for i := 1 to a.Length 
      invariant r == MaxMin(a, i)
      invariant r.0 < r.1
    {
        r := intersect(r, a[i]);
        if r.0 >= r.1 {
            return (0.0, 0.0);
        }
    }
}

// Computes the intersection of two intervals
function intersect(i: (real, real), j :(real, real)): (real, real)  {
    (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1)
}

// Computes the maximum of the left limit and the minimum of the right limit of a group of intervals.
ghost function MaxMin(a: array<(real, real)>, len : nat := a.Length) : (r: (real, real)) 
  reads a
  requires 1 <= len <= a.Length
  ensures exists i :: 0 <= i < len && r.0 == a[i].0  
  ensures exists i :: 0 <= i < len && r.1 == a[i].1  
  ensures forall i :: 0 <= i < len ==> r.0 >= a[i].0
  ensures forall i :: 0 <= i < len ==> r.1 <= a[i].1
{
    if len == 1 then a[0]
    else var r' := MaxMin(a, len-1);
         intersect(a[len-1], r')
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

    var a3 := new (real, real)[] [(0.0, 0.0), (0.0, 1.0)];
    //@invalid var r3 := IntersectIntervals(a3); should not verify due to precondition violation
}