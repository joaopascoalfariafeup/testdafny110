// Finds the maximum distance between equal elements in a non-empty array.
predicate DistLeq<T(==)>(a: array<T>, d: nat)
  requires a.Length > 0
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> (a[i] == a[j] ==> j - i <= d)
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist < a.Length
  ensures DistLeq(a, maxDist)
  ensures exists i, j :: 0 <= i <= j < a.Length && a[i] == a[j] && j - i == maxDist
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= maxDist < a.Length
    invariant forall p, q :: 0 <= p < i && p < q < a.Length ==> (a[p] == a[q] ==> q - p <= maxDist)
  {
    var j := a.Length - 1;
    var md0 := maxDist;
    while j > i + maxDist
      invariant 0 <= i < a.Length
      invariant 0 <= md0 < a.Length
      invariant maxDist == md0
      invariant i + md0 < j < a.Length
      invariant forall k :: j < k < a.Length ==> a[k] != a[i]
    {
      if (a[j] == a[i]) {
        assert j >= i;
        maxDist := j - i;
        break;
      }
      j := j - 1;    
    }
    assert forall q :: i < q < a.Length ==> (a[i] == a[q] ==> q - i <= maxDist);
  }
  assert DistLeq(a, maxDist);
  assert exists i, j :: 0 <= i <= j < a.Length && a[i] == a[j] && j - i == maxDist;
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
