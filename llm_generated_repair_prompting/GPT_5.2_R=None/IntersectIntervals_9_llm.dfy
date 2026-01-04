// Computes the intersection of two intervals
function intersect(i: (real, real), j: (real, real)): (real, real) {
  (if i.0 > j.0 then i.0 else j.0, if i.1 < j.1 then i.1 else j.1)
}

ghost function maxLowPrefix(a: array<(real, real)>, n: int): real
  requires 0 < n <= a.Length
  reads a
  decreases n
  ensures exists k :: 0 <= k < n && maxLowPrefix(a, n) == a[k].0
  ensures forall k :: 0 <= k < n ==> a[k].0 <= maxLowPrefix(a, n)
{
  if n == 1 then a[0].0
  else
    var m := maxLowPrefix(a, n-1);
    if a[n-1].0 > m then a[n-1].0 else m
}

ghost function minHighPrefix(a: array<(real, real)>, n: int): real
  requires 0 < n <= a.Length
  reads a
  decreases n
  ensures exists k :: 0 <= k < n && minHighPrefix(a, n) == a[k].1
  ensures forall k :: 0 <= k < n ==> a[k].1 >= minHighPrefix(a, n)
{
  if n == 1 then a[0].1
  else
    var m := minHighPrefix(a, n-1);
    if a[n-1].1 < m then a[n-1].1 else m
}

lemma MaxLowPrefixStep(a: array<(real, real)>, n: int)
  requires 0 < n < a.Length
  ensures maxLowPrefix(a, n+1) == (if maxLowPrefix(a, n) > a[n].0 then maxLowPrefix(a, n) else a[n].0)
{
}

lemma MinHighPrefixStep(a: array<(real, real)>, n: int)
  requires 0 < n < a.Length
  ensures minHighPrefix(a, n+1) == (if minHighPrefix(a, n) < a[n].1 then minHighPrefix(a, n) else a[n].1)
{
}

// Monotonicity helpers used to reason about returning early on an empty prefix.
lemma MaxLowPrefixMonotone(a: array<(real, real)>, m: int, n: int)
  requires 0 < m <= n <= a.Length
  ensures maxLowPrefix(a, m) <= maxLowPrefix(a, n)
{
  if m == n {
  } else {
    MaxLowPrefixMonotone(a, m, n-1);
    assert maxLowPrefix(a, n) ==
      (if maxLowPrefix(a, n-1) > a[n-1].0 then maxLowPrefix(a, n-1) else a[n-1].0);
    if maxLowPrefix(a, n-1) > a[n-1].0 {
      // maxLowPrefix(a,n) == maxLowPrefix(a,n-1)
    } else {
      // maxLowPrefix(a,n) == a[n-1].0 >= maxLowPrefix(a,n-1) by definition of max
      assert maxLowPrefix(a, n-1) <= a[n-1].0;
    }
  }
}

lemma MinHighPrefixMonotone(a: array<(real, real)>, m: int, n: int)
  requires 0 < m <= n <= a.Length
  ensures minHighPrefix(a, m) >= minHighPrefix(a, n)
{
  if m == n {
  } else {
    MinHighPrefixMonotone(a, m, n-1);
    assert minHighPrefix(a, n) ==
      (if minHighPrefix(a, n-1) < a[n-1].1 then minHighPrefix(a, n-1) else a[n-1].1);
    if minHighPrefix(a, n-1) < a[n-1].1 {
      // minHighPrefix(a,n) == minHighPrefix(a,n-1)
    } else {
      // minHighPrefix(a,n) == a[n-1].1 <= minHighPrefix(a,n-1) by definition of min
      assert a[n-1].1 <= minHighPrefix(a, n-1);
    }
  }
}

// If there exists a point (lo,hi) with lo < hi contained in all intervals,
// then the "max of lows" is strictly below the "min of highs".
lemma NonEmptyIntersectionImpliesMaxLowLtMinHigh(a: array<(real, real)>, lo: real, hi: real)
  requires a.Length > 0
  requires forall k :: 0 <= k < a.Length ==> lo >= a[k].0 && hi <= a[k].1
  requires lo < hi
  ensures maxLowPrefix(a, a.Length) < minHighPrefix(a, a.Length)
{
  // From containment: maxLowPrefix <= lo and minHighPrefix >= hi
  assert forall k :: 0 <= k < a.Length ==> a[k].0 <= lo;
  assert forall k :: 0 <= k < a.Length ==> a[k].1 >= hi;

  assert forall k :: 0 <= k < a.Length ==> a[k].0 <= maxLowPrefix(a, a.Length);
  assert forall k :: 0 <= k < a.Length ==> a[k].1 >= minHighPrefix(a, a.Length);

  assert maxLowPrefix(a, a.Length) <= lo;
  assert minHighPrefix(a, a.Length) >= hi;

  // Therefore maxLowPrefix < minHighPrefix since lo < hi
  calc {
    maxLowPrefix(a, a.Length);
    <= lo;
    < hi;
    <= minHighPrefix(a, a.Length);
  }
}

// Compute the intersection of a non-empty array of non-empty closed intervals.
// If the intersection is empty, by convention returns (0.0, 0.0).
method IntersectIntervals(a: array<(real, real)>) returns (r: (real, real))
  requires a.Length > 0
  requires forall k :: 0 <= k < a.Length ==> a[k].0 < a[k].1
  ensures r == (0.0, 0.0) ||
          (r.0 < r.1 &&
           forall k :: 0 <= k < a.Length ==> r.0 >= a[k].0 && r.1 <= a[k].1)
  ensures r != (0.0, 0.0) ==> r.0 == maxLowPrefix(a, a.Length) && r.1 == minHighPrefix(a, a.Length)
{
  r := a[0];
  for i := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant r.0 < r.1
    invariant r.0 == maxLowPrefix(a, i)
    invariant r.1 == minHighPrefix(a, i)
    invariant forall k :: 0 <= k < i ==> r.0 >= a[k].0 && r.1 <= a[k].1
  {
    // Help Dafny reason about the tuple update through intersect.
    assert intersect(r, a[i]).0 == (if r.0 > a[i].0 then r.0 else a[i].0);
    assert intersect(r, a[i]).1 == (if r.1 < a[i].1 then r.1 else a[i].1);

    // Connect the update to the ghost characterizations
    MaxLowPrefixStep(a, i);
    MinHighPrefixStep(a, i);

    r := intersect(r, a[i]);

    // Re-establish the functional invariants after assignment
    assert r.0 == maxLowPrefix(a, i+1);
    assert r.1 == minHighPrefix(a, i+1);

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

  // Use the method postcondition + computed characterization
  assert r1 == (0.0, 0.0) || (r1.0 < r1.1 && r1.0 >= 0.0 && r1.1 <= 3.0 && r1.0 >= 1.0 && r1.1 <= 4.0 && r1.0 >= 2.0 && r1.1 <= 5.0);

  // Prove it is non-empty in this concrete case using the characterization
  assert maxLowPrefix(a1, a1.Length) == 2.0;
  assert minHighPrefix(a1, a1.Length) == 3.0;
  assert 2.0 < 3.0;

  // If the method returned empty, it must have encountered some prefix with empty intersection,
  // i.e., some i with maxLowPrefix(a1,i) >= minHighPrefix(a1,i). By monotonicity, this would imply
  // maxLowPrefix(a1,Len) >= minHighPrefix(a1,Len), contradicting 2 < 3 above.
  if r1 == (0.0, 0.0) {
    // Prefix non-emptiness witness (2,3) for the whole array
    assert forall k :: 0 <= k < a1.Length ==> 2.0 >= a1[k].0 && 3.0 <= a1[k].1;
    NonEmptyIntersectionImpliesMaxLowLtMinHigh(a1, 2.0, 3.0);
    assert maxLowPrefix(a1, a1.Length) < minHighPrefix(a1, a1.Length);

    // Now show no prefix can be empty
    var i: int :| 0 < i <= a1.Length && maxLowPrefix(a1, i) >= minHighPrefix(a1, i);
    MaxLowPrefixMonotone(a1, i, a1.Length);
    MinHighPrefixMonotone(a1, i, a1.Length);
    assert maxLowPrefix(a1, a1.Length) >= maxLowPrefix(a1, i);
    assert minHighPrefix(a1, a1.Length) <= minHighPrefix(a1, i);
    calc {
      maxLowPrefix(a1, a1.Length);
      >= maxLowPrefix(a1, i);
      >= minHighPrefix(a1, i);
      >= minHighPrefix(a1, a1.Length);
    }
    assert false;
  }
  assert r1 != (0.0, 0.0);

  assert r1.0 == maxLowPrefix(a1, a1.Length);
  assert r1.1 == minHighPrefix(a1, a1.Length);

  assert r1.0 >= 2.0 && r1.1 <= 3.0;
  assert r1.0 <= 2.0; // since r1.0 is max of {0,1,2}
  assert r1.1 >= 3.0; // since r1.1 is min of {3,4,5}
  assert r1 == (2.0, 3.0);

  // Disjoint intervals
  var a2 := new (real, real)[] [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
  assert a2[..] == [(0.0, 3.0), (1.0, 4.0), (3.0, 5.0)];
  var r2 := IntersectIntervals(a2);

  // If non-empty, would need r2.0 >= 3.0 and r2.1 <= 3.0, impossible with r2.0 < r2.1
  assert r2 == (0.0, 0.0) || (r2.0 < r2.1 && r2.0 >= 3.0 && r2.1 <= 3.0);
  assert r2 == (0.0, 0.0);
}
