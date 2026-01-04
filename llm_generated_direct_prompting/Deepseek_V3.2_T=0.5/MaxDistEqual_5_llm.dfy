// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist < a.Length
  ensures forall i, j :: 0 <= i <= j < a.Length && a[i] == a[j] ==> j - i <= maxDist
  ensures exists i, j :: 0 <= i <= j < a.Length && a[i] == a[j] && j - i == maxDist
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant maxDist < a.Length
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length && a[ii] == a[jj] ==> jj - ii <= maxDist
    invariant exists ii, jj :: 0 <= ii < i && 0 <= jj < a.Length && a[ii] == a[jj] && jj - ii == maxDist
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i <= j < a.Length
      invariant maxDist < a.Length
      invariant forall k :: j < k < a.Length ==> a[k] != a[i]
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length && a[ii] == a[jj] ==> jj - ii <= maxDist
      invariant exists ii, jj :: 0 <= ii < i && 0 <= jj < a.Length && a[ii] == a[jj] && jj - ii == maxDist
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
