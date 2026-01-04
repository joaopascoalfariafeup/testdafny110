// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist < a.Length
  ensures forall i:int, j:int :: 0 <= i < a.Length && i <= j < a.Length && a[i] == a[j] ==> j - i <= maxDist as int
  ensures exists i:int, j:int :: 0 <= i < a.Length && i <= j < a.Length && a[i] == a[j] && maxDist == (j - i) as nat
{
  maxDist := 0;
  ghost var wi: nat := 0;
  ghost var wj: nat := 0;

  for i := 0 to a.Length
    invariant 0 <= maxDist < a.Length
    invariant wi <= wj < a.Length
    invariant a[wi as int] == a[wj as int] && wj - wi == maxDist
    invariant forall p:int, q:int :: 0 <= p < i && p <= q < a.Length && a[p] == a[q] ==> q - p <= maxDist as int
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant 0 <= i < a.Length
      invariant 0 <= maxDist < a.Length
      invariant wi <= wj < a.Length
      invariant a[wi as int] == a[wj as int] && wj - wi == maxDist
      invariant 0 <= j < a.Length
      invariant j >= i + maxDist
      invariant forall k:int :: j < k < a.Length && a[k] == a[i] ==> k - i <= maxDist as int
      decreases j
    {
      if (a[j] == a[i]) {
        assert j >= i;
        maxDist := j - i;
        ghost wi := i as nat;
        ghost wj := j as nat;
        break;
      }
      assert a[j] != a[i];
      j := j - 1;    
    }

    assert forall q:int :: i <= q < a.Length && a[i] == a[q] ==> q - i <= maxDist as int;
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
