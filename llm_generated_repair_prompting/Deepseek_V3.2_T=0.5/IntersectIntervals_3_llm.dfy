// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).
method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
  requires a.Length > 0
  requires forall k :: 0 <= k < a.Length ==> a[k].0 <= a[k].1
  ensures forall k :: 0 <= k < a.Length ==> (r.0 <= a[k].1 && r.1 >= a[k].0) || r == (0.0, 0.0)
  ensures r.0 <= r.1 || r == (0.0, 0.0)
{
    r := a[0];
    var i := 1;
    while i < a.Length 
      invariant 1 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> (r.0 <= a[k].1 && r.1 >= a[k].0) || r == (0.0, 0.0)
      invariant r.0 <= r.1 || r == (0.0, 0.0)
    {
        r := intersect(r, a[i]);
        if r.0 > r.1 {
            r := (0.0, 0.0);
            return;
        }
        i := i + 1;
    }
}

// Computes the intersection of two intervals
function intersect(i: (real, real), j :(real, real)): (real, real)  {
    (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1)
}

// Helper lemma to prove properties of intersect
lemma intersect_properties(i: (real, real), j: (real, real))
  requires i.0 <= i.1 && j.0 <= j.1
  ensures intersect(i, j).0 <= intersect(i, j).1 || intersect(i, j).0 > intersect(i, j).1
  ensures forall k :: k == 0 || k == 1 ==> (intersect(i, j).0 <= i.1 && intersect(i, j).1 >= i.0) || (intersect(i, j).0 <= j.1 && intersect(i, j).1 >= j.0) || intersect(i, j).0 > intersect(i, j).1
{
}

method TestIntersectIntervals()
{
    // Overlaping intervals
    var a1 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
    var r1 := IntersectIntervals(a1);
    // Helper assertions to prove the result
    assert a1[0] == (0.0, 3.0);
    assert a1[1] == (1.0, 4.0);
    assert a1[2] == (2.0, 5.0);
    // Compute step by step
    var step1 := intersect((0.0, 3.0), (1.0, 4.0));
    assert step1 == (1.0, 3.0);
    var step2 := intersect(step1, (2.0, 5.0));
    assert step2 == (2.0, 3.0);
    assert r1 == (2.0, 3.0);

    // Disjoint intervals
    var a2 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
    var r2 := IntersectIntervals(a2);
    // Helper assertions
    assert a2[0] == (0.0, 3.0);
    assert a2[1] == (1.0, 4.0);
    assert a2[2] == (3.0, 5.0);
    // Compute step by step
    var step1b := intersect((0.0, 3.0), (1.0, 4.0));
    assert step1b == (1.0, 3.0);
    var step2b := intersect(step1b, (3.0, 5.0));
    assert step2b == (3.0, 3.0);
    // Since 3.0 > 3.0 is false, but 3.0 >= 3.0 is true, the intersection is non-empty? Wait, the condition is r.0 > r.1 for empty.
    // Actually (3.0, 3.0) has r.0 == r.1, so it's non-empty. But the intervals (0.0,3.0), (1.0,4.0), (3.0,5.0) intersect at point 3.0.
    // So the intersection is (3.0, 3.0), not (0.0,0.0). The test expects (0.0,0.0) but that's wrong! The intervals are not disjoint; they intersect at 3.0.
    // Let me check: (0.0,3.0) ∩ (1.0,4.0) ∩ (3.0,5.0) = [max(0.0,1.0,3.0), min(3.0,4.0,5.0)] = [3.0, 3.0]. So the test assertion is incorrect.
    // But the problem says: "If the intersection is empty, by convention returns (0.0, 0.0)". Here intersection is not empty.
    // So the test is wrong. Let me fix the test to use truly disjoint intervals.
    // Change a2 to: [(0.0, 1.0), (2.0, 3.0), (4.0, 5.0)]
    var a2_fixed := new (real, real)[] [(0.0, 1.0), (2.0, 3.0), (4.0, 5.0)];
    var r2_fixed := IntersectIntervals(a2_fixed);
    assert r2_fixed == (0.0, 0.0);
}
