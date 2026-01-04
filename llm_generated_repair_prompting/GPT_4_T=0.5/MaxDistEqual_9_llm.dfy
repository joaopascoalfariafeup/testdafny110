
// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist <= a.Length - 1
  ensures forall i, j :: 0 <= i < j < a.Length && a[i] == a[j] ==> j - i <= maxDist
  ensures (exists i, j :: 0 <= i < j < a.Length && a[i] == a[j] && maxDist == j - i) || (maxDist == 0 && forall i, j :: 0 <= i < j < a.Length ==> a[i] != a[j])
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k, l :: 0 <= k < l < i && a[k] == a[l] ==> l - k <= maxDist
    invariant (exists k, l :: 0 <= k < l < i && a[k] == a[l] && maxDist == l - k) || (maxDist == 0 && forall k, l :: 0 <= k < l < i ==> a[k] != a[l])
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i <= j < a.Length
      invariant forall k :: i <= k < j && a[k] == a[i] ==> k - i <= maxDist
      invariant (exists k :: i <= k < j && a[k] == a[i] && maxDist == k - i) || (maxDist == 0 && forall k :: i <= k < j ==> a[k] != a[i])
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
        assert forall k, l :: 0 <= k < l <= i && a[k] == a[l] ==> l - k <= maxDist; // helper
        assert (exists k, l :: 0 <= k < l <= i && a[k] == a[l] && maxDist == l - k) || (maxDist == 0 && forall k, l :: 0 <= k < l <= i ==> a[k] != a[l]); // helper
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
    assert a1[..] == [1, 2, 1, 2, 2]; // helper
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[..] == [3, 3, 3, 3]; // helper
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert a3[..] == [1, 2, 3, 4]; // helper
    assert d3 == 0; // a[i] to a[i]
}

