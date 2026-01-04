// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist <= a.Length - 1
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] ==> (if i <= j then j - i else i - j) <= maxDist
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] && (if i <= j then j - i else i - j) == maxDist
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= maxDist <= a.Length - 1
    invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < a.Length && a[i0] == a[j0] ==> (if i0 <= j0 then j0 - i0 else i0 - j0) <= maxDist
    invariant exists i0, j0 :: 0 <= i0 < a.Length && 0 <= j0 < a.Length && a[i0] == a[j0] && (if i0 <= j0 then j0 - i0 else i0 - j0) == maxDist
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant 0 <= i <= a.Length
      invariant 0 <= maxDist <= a.Length - 1
      invariant 0 <= j < a.Length
      invariant j + 1 <= a.Length
      invariant i + maxDist < j + 1
      invariant forall k :: j < k < a.Length ==> a[k] != a[i]
      invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < a.Length && a[i0] == a[j0] ==> (if i0 <= j0 then j0 - i0 else i0 - j0) <= maxDist
      invariant exists i0, j0 :: 0 <= i0 < a.Length && 0 <= j0 < a.Length && a[i0] == a[j0] && (if i0 <= j0 then j0 - i0 else i0 - j0) == maxDist
      decreases j
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
