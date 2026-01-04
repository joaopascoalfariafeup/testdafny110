// Finds the maximum distance between equal elements in a non-empty array.

ghost predicate HasDistanceD<T(==)>(a: array<T>, d: nat)
  reads a
{
  exists i, j :: 0 <= i < j < a.Length && j - i == d && a[i] == a[j]
}

ghost predicate MaxDistIs<T(==)>(a: array<T>, d: nat)
  reads a
{
  (d == 0 || HasDistanceD(a, d)) &&
  (forall i, j :: 0 <= i < j < a.Length && a[i] == a[j] ==> j - i <= d)
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  ensures MaxDistIs(a, maxDist)
  ensures maxDist < a.Length || a.Length == 0
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant maxDist <= a.Length || a.Length == 0
    invariant maxDist == 0 || HasDistanceD(a, maxDist)
    invariant forall i', j' :: 0 <= i' < i && i' < j' < a.Length && a[i'] == a[j'] ==> j' - i' <= maxDist
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i <= j < a.Length || j == i + maxDist
      invariant forall j' :: j < j' < a.Length && a[i] == a[j'] ==> j' - i <= maxDist
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
        break;
      }
      j := j - 1;    
    }
  }
}

method {:fuel HasDistanceD<int>, 4} {:fuel MaxDistIs<int>, 4} testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    var d1 := MaxDistEqual(a1);
    assert a1[1] == a1[4] && 4 - 1 == 3;
    assert HasDistanceD(a1, 3);
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[0] == a2[3] && 3 - 0 == 3;
    assert HasDistanceD(a2, 3);
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert d3 == 0; // a[i] to a[i]
}
