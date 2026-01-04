// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist <= a.Length - 1
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] ==> maxDist >= (if i <= j then j - i else i - j)
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] && maxDist == (if i <= j then j - i else i - j)
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant maxDist <= a.Length - 1
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length && a[ii] == a[jj] ==> maxDist >= (if ii <= jj then jj - ii else ii - jj)
    invariant exists ii, jj :: 0 <= ii <= (if i == 0 then 0 else i - 1) && 0 <= jj < a.Length && a[ii] == a[jj] && maxDist == (if ii <= jj then jj - ii else ii - jj)
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant 0 <= i < a.Length
      invariant 0 <= j < a.Length
      invariant maxDist <= a.Length - 1
      invariant i + maxDist < j + 1
      invariant forall k :: j < k < a.Length ==> a[k] != a[i]
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
