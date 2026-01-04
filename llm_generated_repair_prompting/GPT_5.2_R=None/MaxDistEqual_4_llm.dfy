// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist < a.Length
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] ==> (if i <= j then j - i else i - j) <= maxDist
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] && (if i <= j then j - i else i - j) == maxDist
{
  maxDist := 0;

  // Establish initial witness for the "exists" property when maxDist == 0
  assert 0 <= 0 < a.Length;
  assert a[0] == a[0];
  assert (if 0 <= 0 then 0 - 0 else 0 - 0) == maxDist;

  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= maxDist < a.Length
    invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
    // For the processed prefix [0..i), some pair attains maxDist
    invariant exists p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] && (if p <= q then q - p else p - q) == maxDist
  {
    var j := a.Length - 1;

    while j > i + maxDist
      invariant 0 <= i < a.Length
      invariant 0 <= maxDist < a.Length
      invariant 0 <= j < a.Length
      invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
      invariant exists p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] && (if p <= q then q - p else p - q) == maxDist
      // We've already ruled out equality with a[i] for positions past j that are far enough to improve maxDist
      invariant forall k :: j < k < a.Length && i + maxDist < k ==> a[k] != a[i]
    {
      if (a[j] == a[i]) {
        // We found a better distance than the current maxDist (since j > i + maxDist).
        assert j > i + maxDist;
        assert j - i > maxDist;

        maxDist := j - i;

        // Re-establish the "exists" invariant for the outer loop with witness (i,j)
        assert 0 <= i < i + 1;
        assert i + 1 <= a.Length;
        assert 0 <= j < a.Length;
        assert a[i] == a[j];
        assert (if i <= j then j - i else i - j) == maxDist;

        break;
      }
      j := j - 1;
    }

    // If maxDist was not updated in this iteration, the previous witness still works,
    // and since i increases, its p < i requirement remains true next iteration.
  }
}

method testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    assert a1[..] == [1,2,1,2,2];
    var d1 := MaxDistEqual(a1);
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    assert a2[..] == [3,3,3,3];
    var d2 := MaxDistEqual(a2);
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    assert a3[..] == [1,2,3,4];
    var d3 := MaxDistEqual(a3);
    assert d3 == 0; // a[i] to a[i]
}
