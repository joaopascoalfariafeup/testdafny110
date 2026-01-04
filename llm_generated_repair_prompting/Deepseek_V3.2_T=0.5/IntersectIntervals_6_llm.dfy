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
{
}

// Helper lemma to prove that intersect preserves the invariant
lemma intersect_preserves_invariant(r: (real, real), interval: (real, real), k: int, a: array<(real, real)>)
  requires 0 <= k < a.Length
  requires a[k].0 <= a[k].1
  requires interval.0 <= interval.1
  requires forall k' :: 0 <= k' < k ==> (r.0 <= a[k'].1 && r.1 >= a[k'].0) || r == (0.0, 0.0)
  requires r.0 <= r.1 || r == (0.0, 0.0)
  requires interval == a[k]
  ensures (intersect(r, interval).0 <= a[k].1 && intersect(r, interval).1 >= a[k].0) || intersect(r, interval) == (0.0, 0.0)
{
  if r == (0.0, 0.0) {
    // If r is already (0.0,0.0), then intersect(r, interval) will also be (0.0,0.0) because intersect returns (0.0,0.0) only if r is (0.0,0.0)?
    // Actually intersect doesn't change to (0.0,0.0) automatically. But if r is (0.0,0.0), then intersect(r, interval) = (max(0.0, interval.0), min(0.0, interval.1))
    // This might not be (0.0,0.0). So we need to handle this case differently.
    // Actually the invariant says "r == (0.0, 0.0)" as an alternative, so if r is (0.0,0.0), the invariant holds for all k.
    // But in the loop, when we compute intersect(r, a[i]), if r is (0.0,0.0), then intersect(r, a[i]) = (max(0.0, a[i].0), min(0.0, a[i].1))
    // Since a[i].0 >= 0? Not necessarily. So this could break the invariant.
    // Let's re-examine: The invariant says for all k < i, either (r.0 <= a[k].1 && r.1 >= a[k].0) OR r == (0.0,0.0).
    // If r is (0.0,0.0), then the OR holds. So after computing new_r = intersect(r, a[i]), we need to check if new_r is (0.0,0.0) or satisfies the condition.
    // But if r is (0.0,0.0), then new_r might not be (0.0,0.0). However, the loop would have returned earlier because when r becomes (0.0,0.0), we return immediately.
    // Actually in the code: if r.0 > r.1 { r := (0.0, 0.0); return; }
    // So r only becomes (0.0,0.0) when we detect empty intersection and return immediately.
    // Therefore, in the loop body, r is never (0.0,0.0) when we reach the statement r := intersect(r, a[i]).
    // So we can assume r.0 <= r.1.
  }
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
    // Additional helper to connect the method result
    // We need to prove that the method returns step2
    // Since the method processes intervals sequentially, and the intersection is associative,
    // we can assert that the method's result equals the overall intersection.
    // But Dafny doesn't know that automatically. We can add a lemma or use the postconditions.
    // Let's use the postcondition: for all k, (r1.0 <= a1[k].1 && r1.1 >= a1[k].0) || r1 == (0.0,0.0)
    // For k=0: (r1.0 <= 3.0 && r1.1 >= 0.0) or r1==(0.0,0.0)
    // For k=1: (r1.0 <= 4.0 && r1.1 >= 1.0) or r1==(0.0,0.0)
    // For k=2: (r1.0 <= 5.0 && r1.1 >= 2.0) or r1==(0.0,0.0)
    // Also r1.0 <= r1.1 or r1==(0.0,0.0)
    // We know the intersection is non-empty, so r1 != (0.0,0.0). Therefore:
    assert r1 != (0.0, 0.0);
    assert r1.0 <= r1.1;
    assert r1.0 <= 3.0 && r1.1 >= 0.0;
    assert r1.0 <= 4.0 && r1.1 >= 1.0;
    assert r1.0 <= 5.0 && r1.1 >= 2.0;
    // Now we need to show that r1 is exactly (2.0,3.0). 
    // The intersection of all intervals is (2.0,3.0). So we need to prove that any interval satisfying these constraints and being the intersection must be (2.0,3.0).
    // Specifically, r1.0 must be at least 2.0 (because it must be >= 2.0 from k=2) and at most 2.0 (because it must be <= 2.0? Actually from k=0 and k=1, we don't have an upper bound on r1.0).
    // Wait: from k=0: r1.0 <= 3.0, from k=1: r1.0 <= 4.0, from k=2: r1.0 <= 5.0. So the upper bound is 3.0? No, the upper bound on r1.0 is the minimum of the upper bounds of the intervals? Actually r1.0 is the left endpoint of the intersection, which is the maximum of the left endpoints.
    // The left endpoint must be >= each left endpoint: so r1.0 >= 0.0, r1.0 >= 1.0, r1.0 >= 2.0. So r1.0 >= 2.0.
    // The right endpoint must be <= each right endpoint: so r1.1 <= 3.0, r1.1 <= 4.0, r1.1 <= 5.0. So r1.1 <= 3.0.
    // Also r1.0 <= r1.1.
    // The largest possible interval satisfying these is (2.0,3.0). But the method returns the actual intersection, which is exactly (2.0,3.0).
    // To prove this, we need to show that the method's algorithm computes exactly that.
    // We can do it by unfolding the loop:
    // Let's manually simulate the loop with assertions.
    // But since the method is already verified, we can trust its result.
    // However, the test assertion fails because Dafny cannot connect the step-by-step computation with the method result.
    // We can add a ghost variable in the method to track the intersection, but we cannot change the method body.
    // Alternatively, we can prove a lemma that the intersection is unique.
    // Let's add a lemma:
    // lemma intersection_unique(a: array<(real, real)>, r1: (real, real), r2: (real, real))
    // But that's heavy.
    // Instead, we can assert that r1 equals the computed step2 using the fact that the method's postconditions and the properties of intersect.
    // Since the method processes intervals sequentially, and intersect is associative, we can prove by induction.
    // But for the test, we can simply assert the equality and see if Dafny accepts it with additional hints.
    // Let's add:
    assert r1.0 >= 2.0;
    assert r1.1 <= 3.0;
    // Now we have: 2.0 <= r1.0 <= r1.1 <= 3.0
    // Also, from the definition of intersect, the left endpoint is the maximum of all left endpoints, and the right endpoint is the minimum of all right endpoints.
    // The maximum left endpoint is 2.0, and the minimum right endpoint is 3.0.
    // So r1.0 must be exactly 2.0 and r1.1 must be exactly 3.0.
    // We can assert that if an interval [L,R] satisfies L >= 2.0, R <= 3.0, and L <= R, and also L is the maximum left endpoint and R is the minimum right endpoint, then L=2.0 and R=3.0.
    // But Dafny needs help with real numbers.
    // Let's use a simple fact: if L >= 2.0 and L <= 3.0 and L is the maximum of {0.0,1.0,2.0}, then L must be 2.0.
    // Similarly for R.
    // We can write:
    assert r1.0 == 2.0 || r1.0 > 2.0;
    if r1.0 > 2.0 {
        // Then r1.0 > 2.0, but then r1.0 <= r1.1 <= 3.0, so that's possible? For example, (2.5,3.0) satisfies all constraints? Let's check:
        // For k=2: left endpoint is 2.0, so we need r1.0 >= 2.0: 2.5 >= 2.0 OK.
        // For k=0: right endpoint is 3.0, so r1.1 <= 3.0: 3.0 <= 3.0 OK.
        // But is (2.5,3.0) the intersection of all three intervals? No, because the intersection of [0,3], [1,4], [2,5] is [2,3]. (2.5,3.0) is a subset, but not the entire intersection.
        // The method returns the intersection, which is the largest possible interval that is contained in all intervals.
        // So it must be exactly [2,3]. But our postconditions don't guarantee that it's the largest.
        // Indeed, the postcondition only says that for each interval, r overlaps with it or r is (0.0,0.0). It doesn't say that r is the intersection.
        // So the test assertion might be too strong given the postconditions.
        // However, the method actually computes the intersection. So we need to strengthen the postcondition.
        // Let's add a postcondition that r is contained in every interval (if non-empty).
        // But the current postcondition already says: forall k, (r.0 <= a[k].1 && r.1 >= a[k].0) which means r overlaps with each interval? Actually that means the interval [r.0, r.1] overlaps with [a[k].0, a[k].1]. For containment, we need r.0 >= a[k].0 and r.1 <= a[k].1.
        // So the current postcondition is wrong! It should be: forall k, (r.0 >= a[k].0 && r.1 <= a[k].1) || r == (0.0,0.0)
        // Let's change the postcondition.
        // But we are not allowed to change the method under verification? The problem says: "Do not change the Dafny program under verification (namely the algorithms in method bodies); your role is just to fix the annotations needed for successful verification!"
        // So we can change preconditions, postconditions, loop invariants, and add auxiliary declarations.
        // So we should change the postcondition to correctly specify the intersection.
        // However, the test assertions are based on the actual intersection, so they will pass with the correct postcondition.
        // Let's update the postcondition in the method.
    }
}

// We need to fix the postcondition and loop invariant.
// The correct specification: 
// If the intersection of all intervals is non-empty, then r is that intersection (i.e., r.0 = max(a[*].0) and r.1 = min(a[*].1)).
// If the intersection is empty, then r = (0.0,0.0).
// But we can specify it as:
//   ensures (forall k :: 0 <= k < a.Length ==> r.0 >= a[k].0 && r.1 <= a[k].1) || r == (0.0,0.0)
//   ensures r.0 <= r.1 || r == (0.0,0.0)
// And also that if r != (0.0,0.0), then r is the largest such interval? Actually the intersection is unique, so we don't need to specify largest.
// So let's change the postconditions accordingly.

// But we must also update the loop invariant to match.
// The loop invariant should be: for all k < i, r.0 >= a[k].0 && r.1 <= a[k].1 (if r != (0.0,0.0)).
// However, when r becomes (0.0,0.0), we return immediately, so in the loop we can assume r.0 <= r.1 and r != (0.0,0.0) until we possibly set it to (0.0,0.0) and return.
// So let's rewrite the method with corrected annotations.

// Actually, we are allowed to change annotations, so let's do it.

method IntersectIntervals_correct(a: array<(real, real)>) returns (r : (real, real))
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

// Now we need to prove that the loop invariant is maintained.
// When we update r to intersect(r, a[i]), we need to show that for all k < i+1, new_r.0 >= a[k].0 and new_r.1 <= a[k].1.
// For k < i, we have by induction that old_r.0 >= a[k].0 and old_r.1 <= a[k].1.
// Since new_r.0 = max(old_r.0, a[i].0) >= old_r.0 >= a[k].0, and new_r.1 = min(old_r.1, a[i]