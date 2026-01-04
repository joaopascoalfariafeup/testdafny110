// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist < a.Length
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] ==> (if i <= j then j - i else i - j) <= maxDist
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] == a[j] && (if i <= j then j - i else i - j) == maxDist
{
  maxDist := 0;

  for i := 0 to a.Length
    invariant 0 <= maxDist < a.Length
    invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
    // witness: any index equals itself gives distance 0, so it equals current maxDist when maxDist==0,
    // and later the witness can be preserved by updates to maxDist
    invariant exists p, q :: 0 <= p < a.Length && 0 <= q < a.Length && a[p] == a[q] && (if p <= q then q - p else p - q) == maxDist
  {
    var j := a.Length - 1;

    while j > i + maxDist
      invariant 0 <= i <= a.Length
      invariant 0 <= maxDist < a.Length
      invariant 0 <= j < a.Length
      invariant j + 1 <= a.Length
      invariant i + maxDist < a.Length ==> i + maxDist < j + 1
      invariant forall p, q :: 0 <= p < i && 0 <= q < a.Length && a[p] == a[q] ==> (if p <= q then q - p else p - q) <= maxDist
      invariant exists p, q :: 0 <= p < a.Length && 0 <= q < a.Length && a[p] == a[q] && (if p <= q then q - p else p - q) == maxDist
      invariant forall k :: j < k < a.Length && i + maxDist < k && k > i ==> a[k] != a[i]
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
        break;
      }
      j := j - 1;
    }

    // Help the verifier establish the "exists" invariant for the next iteration when maxDist may stay 0.
    if maxDist == 0 {
      assert 0 <= 0 < a.Length;
      assert a[0] == a[0];
      assert (if 0 <= 0 then 0 - 0 else 0 - 0) == 0;
    }
  }
}

method testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    assert a1[..] == [1,2,1,2,2];
    var d1 := MaxDistEqual(a1);
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    assert a2[..] == [3,3,3,3];
    var d2 := MaxDistEqual(a2);
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    assert a3[..] == [1,2,3,4];
    var d3 := MaxDistEqual(a3);
    assert d3 == 0; // a[i] to a[i]
}
