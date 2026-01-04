// Finds the maximum distance between equal elements in a non-empty array.

ghost predicate HasPairWithDist<T(==)>(a: array<T>, d: nat)
  reads a
{
  exists i, j :: 0 <= i < j < a.Length && j - i == d && a[i] == a[j]
}

ghost predicate IsMaxDist<T(==)>(a: array<T>, maxDist: nat)
  reads a
{
  (maxDist == 0 || HasPairWithDist(a, maxDist)) &&
  (forall i, j :: 0 <= i < j < a.Length && a[i] == a[j] ==> j - i <= maxDist)
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  ensures maxDist <= if a.Length == 0 then 0 else a.Length - 1
  ensures maxDist == 0 || HasPairWithDist(a, maxDist)
  ensures forall i, j :: 0 <= i < j < a.Length && a[i] == a[j] ==> j - i <= maxDist
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant maxDist <= if a.Length == 0 then 0 else a.Length - 1
    invariant maxDist == 0 || HasPairWithDist(a, maxDist)
    invariant forall i', j :: 0 <= i' < i && i' < j < a.Length && a[i'] == a[j] ==> j - i' <= maxDist
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i <= j < a.Length || j == i - 1
      invariant forall k :: j < k < a.Length && k > i + maxDist ==> a[k] != a[i] || k - i <= maxDist
      invariant forall k :: j < k < a.Length && a[i] == a[k] ==> k - i <= maxDist
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
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
    assert a1[1] == a1[4] && 4 - 1 == 3;
    assert HasPairWithDist(a1, 3);
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[0] == a2[3] && 3 - 0 == 3;
    assert HasPairWithDist(a2, 3);
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert d3 == 0; // a[i] to a[i]
}
