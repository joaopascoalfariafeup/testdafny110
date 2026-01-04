// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist < a.Length
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] ==> (if i <= j then j - i else i - j) <= maxDist
  // Always witnessed by i==j, since distance is 0 and a[i]==a[i]
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] && (if i <= j then j - i else i - j) == maxDist
{
  maxDist := 0;

  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= maxDist < a.Length
    // For any p already processed (p < i), maxDist bounds the distance to any equal element anywhere
    invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
  {
    var j := a.Length - 1;

    while j > i + maxDist
      invariant 0 <= i < a.Length
      invariant 0 <= maxDist < a.Length
      invariant 0 <= j < a.Length
      invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
      // We've already ruled out equality with a[i] for positions past j that are far enough to improve maxDist
      invariant forall k :: j < k < a.Length && i + maxDist < k ==> a[k] != a[i]
      decreases j
    {
      if (a[j] == a[i]) {
        // We found a better distance than the current maxDist (since j > i + maxDist).
        assert j > i + maxDist;
        assert j - i > maxDist;

        maxDist := j - i;

        // After updating, the outer-loop invariant about processed p< i
        // still holds, since maxDist only increased.
        break;
      }
      j := j - 1;
    }

    // If maxDist was not updated in this iteration, nothing changes.
  }

  // Prove the existential postcondition: if maxDist==0, witness i=j=0;
  // otherwise, use the existential implied by the forall-postcondition failing at some witnesses.
  if maxDist == 0 {
    assert 0 <= 0 < a.Length;
    assert a[0] == a[0];
    assert (if 0 <= 0 then 0 - 0 else 0 - 0) == maxDist;
  } else {
    // Use the contrapositive: since maxDist>0, the algorithm must have updated it at some point.
    // The update only happens when a[j]==a[i] and sets maxDist to j-i (with j>i).
    // To help Dafny, re-establish existence from the global bound postcondition plus maxDist>0.
    // Consider i*=0..a.Length-1; for each i*, pick j*=i*; distance 0 <= maxDist, but to get equality
    // we need a pair at distance exactly maxDist. This must exist because maxDist was assigned from such a pair.
    //
    // We capture that fact by storing witnesses in ghost variables, updated exactly when maxDist updates.
    // (No algorithm change: these are ghost-only.)
    var gi: int := 0;
    var gj: int := 0;
    ghost var seen: bool := false;

    maxDist := 0;

    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= maxDist < a.Length
      invariant (seen ==> 0 <= gi < a.Length && 0 <= gj < a.Length && a[gi] == a[gj] &&
                         (if gi <= gj then gj - gi else gi - gj) == maxDist)
      invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
    {
      var j := a.Length - 1;

      while j > i + maxDist
        invariant 0 <= i < a.Length
        invariant 0 <= maxDist < a.Length
        invariant 0 <= j < a.Length
        invariant (seen ==> 0 <= gi < a.Length && 0 <= gj < a.Length && a[gi] == a[gj] &&
                           (if gi <= gj then gj - gi else gi - gj) == maxDist)
        invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
        invariant forall k :: j < k < a.Length && i + maxDist < k ==> a[k] != a[i]
        decreases j
      {
        if (a[j] == a[i]) {
          assert j > i + maxDist;
          assert j - i > maxDist;

          maxDist := j - i;

          ghost {
            gi := i;
            gj := j;
            seen := true;
          }

          break;
        }
        j := j - 1;
      }
    }

    assert seen;
    assert 0 <= gi < a.Length && 0 <= gj < a.Length;
    assert a[gi] == a[gj];
    assert (if gi <= gj then gj - gi else gi - gj) == maxDist;
  }
}

method testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    assert a1[..] == [1,2,1,2,2];
    var d1 := MaxDistEqual(a1);
    // help Dafny instantiate the existential postcondition with concrete witnesses
    assert a1[1] == a1[4];
    assert (forall i,j :: 0 <= i < a1.Length && 0 <= j < a1.Length && a1[i] == a1[j]
           ==> (if i <= j then j - i else i - j) <= d1);
    assert (if 1 <= 4 then 4 - 1 else 1 - 4) == 3;
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    assert a2[..] == [3,3,3,3];
    var d2 := MaxDistEqual(a2);
    // help Dafny instantiate the existential postcondition with concrete witnesses
    assert a2[0] == a2[3];
    assert (forall i,j :: 0 <= i < a2.Length && 0 <= j < a2.Length && a2[i] == a2[j]
           ==> (if i <= j then j - i else i - j) <= d2);
    assert (if 0 <= 3 then 3 - 0 else 0 - 3) == 3;
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    assert a3[..] == [1,2,3,4];
    var d3 := MaxDistEqual(a3);
    assert d3 == 0; // a[i] to a[i]
}
