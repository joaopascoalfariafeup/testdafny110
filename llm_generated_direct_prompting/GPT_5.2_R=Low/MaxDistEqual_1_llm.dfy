// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  ensures a.Length == 0 ==> maxDist == 0
  ensures a.Length > 0 ==> maxDist <= a.Length - 1
  ensures forall i, j :: 0 <= i < a.Length && i <= j < a.Length && a[i] == a[j] ==> j - i <= maxDist
  ensures a.Length > 0 ==> exists i, j :: 0 <= i < a.Length && i <= j < a.Length && a[i] == a[j] && maxDist == j - i
{
  maxDist := 0;

  ghost var wi: int := 0;
  ghost var wj: int := 0;

  for i := 0 to a.Length
    invariant 0 <= maxDist
    invariant a.Length == 0 ==> maxDist == 0
    invariant a.Length > 0 ==> maxDist <= a.Length - 1
    invariant forall p, q :: 0 <= p < i && p <= q < a.Length && a[p] == a[q] ==> q - p <= maxDist
    invariant a.Length > 0 ==> 0 <= wi < a.Length && wi <= wj < a.Length && a[wi] == a[wj] && maxDist == wj - wi
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant 0 <= i < a.Length
      invariant 0 <= maxDist
      invariant a.Length == 0 ==> maxDist == 0
      invariant a.Length > 0 ==> maxDist <= a.Length - 1
      invariant 0 <= j < a.Length
      invariant i + maxDist < a.Length
      invariant j >= 0
      invariant j > i + maxDist
      invariant forall k :: j < k < a.Length ==> a[k] != a[i]
      decreases j
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
        ghost wi := i;
        ghost wj := j;
        break;
      }
      j := j - 1;    
    }

    assert forall q :: i <= q < a.Length && a[i] == a[q] ==> q - i <= maxDist;
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
