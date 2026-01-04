// Compute the intersection of a non-empty array of non-empty closed intervals. 
// If the intersection is empty, by convention returns (0.0, 0.0).
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
      invariant r.0 == maxLeftSeq(a[..i]) && r.1 == minRightSeq(a[..i])
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

// Ghost functions for max left and min right for sequences
ghost function maxLeftSeq(s: seq<(real, real)>) : real
  requires |s| > 0
  ensures forall k :: 0 <= k < |s| ==> maxLeftSeq(s) >= s[k].0
  ensures exists k :: 0 <= k < |s| && maxLeftSeq(s) == s[k].0
{
  if |s| == 1 then s[0].0
  else
    var m := maxLeftSeq(s[..|s|-1]);
    if s[|s|-1].0 > m then s[|s|-1].0 else m
}

ghost function minRightSeq(s: seq<(real, real)>) : real
  requires |s| > 0
  ensures forall k :: 0 <= k < |s| ==> minRightSeq(s) <= s[k].1
  ensures exists k :: 0 <= k < |s| && minRightSeq(s) == s[k].1
{
  if |s| == 1 then s[0].1
  else
    var m := minRightSeq(s[..|s|-1]);
    if s[|s|-1].1 < m then s[|s|-1].1 else m
}

// Ghost functions for max left and min right for arrays (using sequences)
ghost function maxLeft(a: array<(real, real)>) : real
  requires a.Length > 0
  reads a
  ensures forall k :: 0 <= k < a.Length ==> maxLeft(a) >= a[k].0
  ensures exists k :: 0 <= k < a.Length && maxLeft(a) == a[k].0
{
  maxLeftSeq(a[..])
}

ghost function minRight(a: array<(real, real)>) : real
  requires a.Length > 0
  reads a
  ensures forall k :: 0 <= k < a.Length ==> minRight(a) <= a[k].1
  ensures exists k :: 0 <= k < a.Length && minRight(a) == a[k].1
{
  minRightSeq(a[..])
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
    // Compute maxLeft and minRight
    var L := maxLeft(a1);
    var R := minRight(a1);
    // Prove L == 2.0 and R == 3.0
    assert a1[..] == [(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)];
    // Use fuel to help Dafny compute maxLeftSeq and minRightSeq
    ghost function {:fuel 3} maxLeftSeqFuel(s: seq<(real, real)>) : real
      requires |s| > 0
      ensures maxLeftSeqFuel(s) == maxLeftSeq(s)
    {
      maxLeftSeq(s)
    }
    ghost function {:fuel 3} minRightSeqFuel(s: seq<(real, real)>) : real
      requires |s| > 0
      ensures minRightSeqFuel(s) == minRightSeq(s)
    {
      minRightSeq(s)
    }
    assert maxLeftSeqFuel([(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)]) == 2.0;
    assert minRightSeqFuel([(0.0, 3.0), (1.0, 4.0), (2.0, 5.0)]) == 3.0;
    assert L == 2.0;
    assert R == 3.0;
    // Now by postcondition, if r1 != (0.0,0.0) then r1.0 == L and r1.1 == R.
    // We know the intersection is non-empty because L <= R.
    assert L <= R;
    // Prove r1 != (0.0, 0.0) using the postcondition and the fact that L <= R
    if r1 == (0.0, 0.0) {
        // Then by postcondition, either forall k :: 0 <= k < a1.Length ==> r1.0 >= a1[k].0 && r1.1 <= a1[k].1 is false
        // But if r1 == (0.0,0.0), then r1.0 >= a1[0].0? 0.0 >= 0.0 holds, and r1.1 <= a1[0].1? 0.0 <= 3.0 holds.
        // Actually the postcondition says: (forall k :: ...) || r == (0.0,0.0)
        // So if r == (0.0,0.0) the disjunction holds trivially.
        // However, we also have the third postcondition: r != (0.0,0.0) ==> (r.0 == maxLeft(a) && r.1 == minRight(a))
        // This doesn't give us anything if r == (0.0,0.0).
        // But we know from the method's logic that if the intersection is non-empty, it returns the intersection, not (0.0,0.0).
        // We need to use the fact that the method's loop invariant ensures that when the loop finishes without early return,
        // r.0 <= r.1 and r.0 == maxLeftSeq(a[..a.Length]) and r.1 == minRightSeq(a[..a.Length]).
        // Since L <= R, the method would not have returned early, so r1 != (0.0,0.0).
        // We can prove this by contradiction: assume r1 == (0.0,0.0). Then the method must have returned early.
        // But the early return only happens when r.0 > r.1 after intersect.
        // However, with the given array, the intersection is non-empty, so the condition r.0 > r.1 never occurs.
        // To help Dafny, we add an explicit assertion about the intersection of the first two intervals.
        var temp := intersect((0.0, 3.0), (1.0, 4.0));
        assert temp == (1.0, 3.0);
        assert temp.0 <= temp.1;
        temp := intersect(temp, (2.0, 5.0));
        assert temp == (2.0, 3.0);
        assert temp.0 <= temp.1;
    }
    assert r1 != (0.0, 0.0);
    assert r1.0 == 2.0;
    assert r1.1 == 3.0;
    // Additional test: empty intersection
    var a2 := new (real, real)[] [(0.0, 1.0), (2.0, 3.0)];
    var r2 := IntersectIntervals(a2);
    // The intersection is empty because max left = 2.0, min right = 1.0, and 2.0 > 1.0.
    var L2 := maxLeft(a2);
    var R2 := minRight(a2);
    // Prove L2 == 2.0 and R2 == 1.0
    assert a2[..] == [(0.0, 1.0), (2.0, 3.0)];
    assert maxLeftSeqFuel([(0.0, 1.0), (2.0, 3.0)]) == 2.0;
    assert minRightSeqFuel([(0.0, 1.0), (2.0, 3.0)]) == 1.0;
    assert L2 == 2.0;
    assert R2 == 1.0;
    assert L2 > R2;
    // Therefore, by the method, r2 should be (0.0,0.0).
    assert r2 == (0.0, 0.0);
}


