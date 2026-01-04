// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).
method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
  requires a.Length > 0
  requires forall k :: 0 <= k < a.Length ==> a[k].0 <= a[k].1
  ensures (forall k :: 0 <= k < a.Length ==> r.0 >= a[k].0 && r.1 <= a[k].1) || r == (0.0, 0.0)
  ensures r.0 <= r.1 || r == (0.0, 0.0)
{
    r := a[0];
    var i := 1;
    while i < a.Length 
      invariant 1 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> r.0 >= a[k].0 && r.1 <= a[k].1
      invariant r.0 <= r.1
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
{
}

// Helper lemma to prove that intersect preserves the invariant
lemma intersect_preserves_invariant(r: (real, real), interval: (real, real), k: int, a: array<(real, real)>)
  requires 0 <= k < a.Length
  requires a[k].0 <= a[k].1
  requires interval.0 <= interval.1
  requires forall k' :: 0 <= k' < k ==> (r.0 >= a[k'].0 && r.1 <= a[k'].1)
  requires r.0 <= r.1
  requires interval == a[k]
  ensures (intersect(r, interval).0 >= a[k].0 && intersect(r, interval).1 <= a[k].1)
{
  // The new left endpoint is max(r.0, interval.0) which is >= interval.0
  // The new right endpoint is min(r.1, interval.1) which is <= interval.1
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
    // Use postconditions to deduce properties
    assert r1 != (0.0, 0.0) by {
      if r1 == (0.0, 0.0) {
        // Then by postcondition, for all k, (r1.0 >= a1[k].0 && r1.1 <= a1[k].1) || r1 == (0.0,0.0)
        // But if r1 == (0.0,0.0), the second disjunct holds, so no contradiction.
        // However, we know the intersection is non-empty, so we need to use the fact that the method returns (0.0,0.0) only when intersection is empty.
        // The method returns (0.0,0.0) only when r.0 > r.1 after intersect.
        // But for these intervals, the intersection is non-empty.
        // We can prove by calculation that the intersection is non-empty.
        // Let's compute the overall intersection manually.
        // The maximum left endpoint is 2.0, the minimum right endpoint is 3.0, and 2.0 <= 3.0.
        // So the intersection is non-empty.
        // Therefore, the method cannot return (0.0,0.0).
        // We can assert that:
        assert 2.0 <= 3.0;
        // But Dafny needs more help.
        // Let's use the postcondition: if r1 == (0.0,0.0), then the first postcondition says: forall k, (r1.0 >= a1[k].0 && r1.1 <= a1[k].1) || r1 == (0.0,0.0)
        // This is trivially true because r1 == (0.0,0.0).
        // So we need a stronger postcondition? Actually the postcondition is correct: if intersection is empty, returns (0.0,0.0); if non-empty, returns the intersection.
        // But the postcondition doesn't guarantee that if intersection is non-empty, then r != (0.0,0.0).
        // We need to add that.
        // Let's add a postcondition to IntersectIntervals:
        //   ensures (exists L,R :: L <= R && forall k :: 0 <= k < a.Length ==> L >= a[k].0 && R <= a[k].1) ==> r != (0.0,0.0)
        // But we cannot change the method now? We are allowed to change annotations, so we can add this postcondition.
        // However, the test method is separate. We can instead prove within the test that r1 cannot be (0.0,0.0) by using the fact that the intersection is non-empty.
        // Let's define a ghost function that computes the intersection endpoints.
        ghost function maxLeft(a: array<(real, real)>) : real
          requires a.Length > 0
          ensures forall k :: 0 <= k < a.Length ==> maxLeft(a) >= a[k].0
          ensures exists k :: 0 <= k < a.Length && maxLeft(a) == a[k].0
        {
          if a.Length == 1 then a[0].0
          else
            var m := maxLeft(a[..a.Length-1]);
            if a[a.Length-1].0 > m then a[a.Length-1].0 else m
        }
        ghost function minRight(a: array<(real, real)>) : real
          requires a.Length > 0
          ensures forall k :: 0 <= k < a.Length ==> minRight(a) <= a[k].1
          ensures exists k :: 0 <= k < a.Length && minRight(a) == a[k].1
        {
          if a.Length == 1 then a[0].1
          else
            var m := minRight(a[..a.Length-1]);
            if a[a.Length-1].1 < m then a[a.Length-1].1 else m
        }
        // Now compute for a1
        var L := maxLeft(a1);
        var R := minRight(a1);
        assert L == 2.0;
        assert R == 3.0;
        assert L <= R;
        // Now, if r1 == (0.0,0.0), then by the postcondition, for all k, (0.0 >= a1[k].0 && 0.0 <= a1[k].1) is false because 0.0 >= 2.0? Actually for k=2, a1[2].0 = 2.0, so 0.0 >= 2.0 is false.
        // So the first disjunct (r1.0 >= a1[k].0 && r1.1 <= a1[k].1) is false for k=2.
        // Therefore, the postcondition would require r1 == (0.0,0.0) to hold, which it does.
        // So the postcondition doesn't give a contradiction.
        // We need to add a postcondition that if the intersection is non-empty, then r is that intersection.
        // Let's change the method's postcondition to include that r.0 == maxLeft(a) and r.1 == minRight(a) when r != (0.0,0.0).
        // But we are allowed to change annotations, so let's do it.
        // However, the test is failing because we haven't changed the method yet.
        // Let's assume we have changed the method to have the correct postcondition.
        // For now, we will skip this test and focus on fixing the method.
      }
    }
    // Instead, let's use the corrected method IntersectIntervals_correct.
    // But the test calls IntersectIntervals, not IntersectIntervals_correct.
    // We need to update the test to use the corrected method, or update the original method.
    // Since we are allowed to change annotations, we will update the original method.
    // Let's go back and update IntersectIntervals with stronger postconditions.
}

// We need to add postconditions that specify the intersection precisely.
// Let's define ghost functions for max left and min right.

ghost function maxLeft(a: array<(real, real)>) : real
  requires a.Length > 0
  ensures forall k :: 0 <= k < a.Length ==> maxLeft(a) >= a[k].0
  ensures exists k :: 0 <= k < a.Length && maxLeft(a) == a[k].0
{
  if a.Length == 1 then a[0].0
  else
    var m := maxLeft(a[..a.Length-1]);
    if a[a.Length-1].0 > m then a[a.Length-1].0 else m
}

ghost function minRight(a: array<(real, real)>) : real
  requires a.Length > 0
  ensures forall k :: 0 <= k < a.Length ==> minRight(a) <= a[k].1
  ensures exists k :: 0 <= k < a.Length && minRight(a) == a[k].1
{
  if a.Length == 1 then a[0].1
  else
    var m := minRight(a[..a.Length-1]);
    if a[a.Length-1].1 < m then a[a.Length-1].1 else m
}

// Now update IntersectIntervals with additional postconditions.
method IntersectIntervals(a: array<(real, real)>) returns (r : (real, real))
  requires a.Length > 0
  requires forall k :: 0 <= k < a.Length ==> a[k].0 <= a[k].1
  ensures (forall k :: 0 <= k < a.Length ==> r.0 >= a[k].0 && r.1 <= a[k].1) || r == (0.0, 0.0)
  ensures r.0 <= r.1 || r == (0.0, 0.0)
  ensures r != (0.0, 0.0) ==> (r.0 == maxLeft(a) && r.1 == minRight(a))
{
    r := a[0];
    var i := 1;
    while i < a.Length 
      invariant 1 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> r.0 >= a[k].0 && r.1 <= a[k].1
      invariant r.0 <= r.1
      invariant r.0 == maxLeft(a[..i]) && r.1 == minRight(a[..i])
    {
        r := intersect(r, a[i]);
        if r.0 > r.1 {
            r := (0.0, 0.0);
            return;
        }
        i := i + 1;
    }
}

// Now update the test method to use the new postconditions.
method TestIntersectIntervals()
{
    // Overlaping intervals
    var a1 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
    var r1 := IntersectIntervals(a1);
    // Helper assertions to prove the result
    assert a1[0] == (0.0, 3.0);
    assert a1[1] == (1.0, 4.0);
    assert a1[2] == (2.0, 5.0);
    // Compute maxLeft and minRight
    var L := maxLeft(a1);
    var R := minRight(a1);
    assert L == 2.0;
    assert R == 3.0;
    // Now by postcondition, if r1 != (0.0,0.0) then r1.0 == L and r1.1 == R.
    // We know the intersection is non-empty because L <= R.
    assert L <= R;
    assert r1 != (0.0, 0.0);
    assert r1.0 == 2.0;
    assert r1.1 == 3.0;
    // Additional test: empty intersection
    var a2 := new (real, real)[] [(0.0, 1.0), (2.0, 3.0)];
    var r2 := IntersectIntervals(a2);
    // The intersection is empty because max left = 2.0, min right = 1.0, and 2.0 > 1.0.
    var L2 := maxLeft(a2);
    var R2 := minRight(a2);
    assert L2 == 2.0;
    assert R2 == 1.0;
    assert L2 > R2;
    // Therefore, by the method, r2 should be (0.0,0.0).
    assert r2 == (0.0, 0.0);
}
