// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist < a.Length
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] ==> (if i <= j then j - i else i - j) <= maxDist
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] && (if i <= j then j - i else i - j) == maxDist
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant maxDist < a.Length
    invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
    invariant exists p, q :: 0 <= p < a.Length && 0 <= q < a.Length && a[p] == a[q] && (if p <= q then q - p else p - q) == maxDist
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant 0 <= i <= a.Length
      invariant 0 <= j < a.Length
      invariant maxDist < a.Length
      invariant i + maxDist < a.Length ==> 0 <= i + maxDist < a.Length
      invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
      invariant forall k :: j < k < a.Length && k > i + maxDist ==> a[k] != a[i]
      invariant forall k :: 0 <= k < a.Length && a[k] == a[i] ==> (if i <= k then k - i else i - k) <= (a.Length - 1) - i
      invariant exists p, q :: 0 <= p < a.Length && 0 <= q < a.Length && a[p] == a[q] && (if p <= q then q - p else p - q) == maxDist
      decreases j
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
        assert 0 <= maxDist;
        assert maxDist < a.Length;
        assert forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist;
        assert forall q :: 0 <= q < a.Length && a[i] == a[q] ==> (if i <= q then q - i else i - q) <= maxDist;
        break;
      }
      j := j - 1;    
    }
  }
}

method testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    var d1 := MaxDistEqual(a1);
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert d3 == 0; // a[i] to a[i]
}
