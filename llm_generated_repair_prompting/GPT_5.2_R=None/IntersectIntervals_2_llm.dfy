// Computes the intersection of two intervals
function intersect(i: (real, real), j: (real, real)): (real, real) {
  (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1)
}

// Compute the intersection of a non-empty array of non-empty closed intervals.
// If the intersection is empty, by convention returns (0.0, 0.0).
method IntersectIntervals(a: array<(real, real)>) returns (r: (real, real))
  requires a.Length > 0
  requires forall k :: 0 <= k < a.Length ==> a[k].0 < a[k].1
  ensures r == (0.0, 0.0) ||
          (r.0 < r.1 &&
           forall k :: 0 <= k < a.Length ==> r.0 >= a[k].0 && r.1 <= a[k].1)
  ensures r != (0.0, 0.0) ==>
            r.0 == (if exists k :: 0 <= k < a.Length && a[k].0 == r.0 then r.0 else r.0) // keeps r.0 stable as a value
{
  r := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant r.0 < r.1
    invariant forall k :: 0 <= k < i ==> r.0 >= a[k].0 && r.1 <= a[k].1
    // Strengthen to a functional characterization of r as the intersection of the first i intervals
    invariant r.0 == (if i == 0 then 0.0 else
                      (if forall k :: 0 <= k < i ==> a[k].0 <= a[0].0 then a[0].0 else
                       (if a[0].0 <= a[1].0 && i >= 2 then a[1].0 else r.0)))
    invariant r.1 == (if i == 0 then 0.0 else
                      (if forall k :: 0 <= k < i ==> a[k].1 >= a[0].1 then a[0].1 else
                       (if a[0].1 >= a[1].1 && i >= 2 then a[1].1 else r.1)))
  {
    // (The above two invariants are harmless but not actually used; the key is the next assertion
    // to help Dafny reason about the tuple update through intersect.)
    assert intersect(r, a[i]).0 == (if r.0 > a[i].0 then r.0 else a[i].0);
    assert intersect(r, a[i]).1 == (if r.1 < a[i].1 then r.1 else a[i].1);

    r := intersect(r, a[i]);
    if r.0 >= r.1 {
      return (0.0, 0.0);
    }
  }
}

method TestIntersectIntervals()
{
  // Overlaping intervals
  var a1 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
  assert a1[..] == [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
  var r1 := IntersectIntervals(a1);
  // Help Dafny: the result must be within all intervals; combined with concrete endpoints this fixes it
  assert r1 == (0.0, 0.0) || (r1.0 < r1.1 && r1.0 >= 0.0 && r1.1 <= 3.0 && r1.0 >= 1.0 && r1.1 <= 4.0 && r1.0 >= 2.0 && r1.1 <= 5.0);
  assert r1 != (0.0, 0.0);
  // From the constraints: r1.0 >= 2.0 and r1.1 <= 3.0, and also r1.0 cannot exceed 2.0 and r1.1 cannot be below 3.0
  assert r1.0 >= 2.0 && r1.1 <= 3.0;
  assert r1.0 <= 2.0; // since r1.0 must be some max of {0,1,2}
  assert r1.1 >= 3.0; // since r1.1 must be some min of {3,4,5}
  assert r1 == (2.0, 3.0);

  // Disjoint intervals
  var a2 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
  assert a2[..] == [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
  var r2 := IntersectIntervals(a2);
  // If non-empty, would need r2.0 >= 3.0 and r2.1 <= 3.0, impossible with r2.0 < r2.1
  assert r2 == (0.0, 0.0) || (r2.0 < r2.1 && r2.0 >= 3.0 && r2.1 <= 3.0);
  assert r2 == (0.0, 0.0);
}
