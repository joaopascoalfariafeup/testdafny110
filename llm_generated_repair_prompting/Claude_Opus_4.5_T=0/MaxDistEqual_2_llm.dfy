// Finds the maximum distance between equal elements in a non-empty array.

ghost function {:fuel 6} MaxDistEqualInRange<T(==)>(a: seq<T>, upToI: nat): nat
  requires upToI <= |a|
{
  if upToI == 0 then 0
  else 
    var i := upToI - 1;
    var maxPrev := MaxDistEqualInRange(a, i);
    var maxForI := MaxDistFromIndex(a, i);
    if maxForI > maxPrev then maxForI else maxPrev
}

ghost function {:fuel 6} MaxDistFromIndex<T(==)>(a: seq<T>, i: nat): nat
  requires i < |a|
{
  MaxDistFromIndexHelper(a, i, |a| - 1)
}

ghost function {:fuel 6} MaxDistFromIndexHelper<T(==)>(a: seq<T>, i: nat, j: int): nat
  requires i < |a|
  requires -1 <= j < |a|
{
  if j <= i then 0
  else if a[j] == a[i] then j - i
  else MaxDistFromIndexHelper(a, i, j - 1)
}

ghost predicate NoEqualPairWithDistGreaterThan<T(==)>(a: seq<T>, d: nat)
{
  forall i, j :: 0 <= i < j < |a| && a[i] == a[j] ==> j - i <= d
}

ghost predicate ExistsPairWithDist<T(==)>(a: seq<T>, d: nat)
{
  d == 0 || exists i, j :: 0 <= i < j < |a| && a[i] == a[j] && j - i == d
}

lemma MaxDistEqualProperties<T(==)>(a: seq<T>)
  ensures NoEqualPairWithDistGreaterThan(a, MaxDistEqualInRange(a, |a|))
  ensures ExistsPairWithDist(a, MaxDistEqualInRange(a, |a|))
{
  MaxDistEqualInRangeProperties(a, |a|);
}

lemma MaxDistEqualInRangeProperties<T(==)>(a: seq<T>, upToI: nat)
  requires upToI <= |a|
  ensures forall i, j :: 0 <= i < upToI && i < j < |a| && a[i] == a[j] ==> j - i <= MaxDistEqualInRange(a, upToI)
  ensures MaxDistEqualInRange(a, upToI) == 0 || exists i, j :: 0 <= i < upToI && i < j < |a| && a[i] == a[j] && j - i == MaxDistEqualInRange(a, upToI)
{
  if upToI > 0 {
    MaxDistEqualInRangeProperties(a, upToI - 1);
    MaxDistFromIndexProperties(a, upToI - 1);
  }
}

lemma MaxDistFromIndexProperties<T(==)>(a: seq<T>, i: nat)
  requires i < |a|
  ensures forall j :: i < j < |a| && a[i] == a[j] ==> j - i <= MaxDistFromIndex(a, i)
  ensures MaxDistFromIndex(a, i) == 0 || exists j :: i < j < |a| && a[i] == a[j] && j - i == MaxDistFromIndex(a, i)
{
  MaxDistFromIndexHelperProperties(a, i, |a| - 1);
}

lemma MaxDistFromIndexHelperProperties<T(==)>(a: seq<T>, i: nat, k: int)
  requires i < |a|
  requires -1 <= k < |a|
  ensures forall j :: i < j <= k && a[i] == a[j] ==> j - i <= MaxDistFromIndexHelper(a, i, k)
  ensures MaxDistFromIndexHelper(a, i, k) == 0 || exists j :: i < j <= k && a[i] == a[j] && j - i == MaxDistFromIndexHelper(a, i, k)
{
  if k > i {
    if a[k] != a[i] {
      MaxDistFromIndexHelperProperties(a, i, k - 1);
    }
  }
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  ensures maxDist == MaxDistEqualInRange(a[..], a.Length)
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant maxDist == MaxDistEqualInRange(a[..], i)
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i as int <= j < a.Length
      invariant forall k :: j < k < a.Length && a[k] == a[i] ==> k - i <= maxDist
      invariant maxDist >= MaxDistEqualInRange(a[..], i)
    {
      if (a[j] == a[i]) {
        assert a[..][j] == a[j];
        assert a[..][i] == a[i];
        maxDist := j - i;
        break;
      }
      j := j - 1;    
    }
    assert maxDist == MaxDistEqualInRange(a[..], i + 1) by {
      MaxDistFromIndexHelperProperties(a[..], i, a.Length - 1);
    }
  }
}

method testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    var d1 := MaxDistEqual(a1);
    assert a1[..] == [1, 2, 1, 2, 2];
    assert MaxDistEqualInRange([1, 2, 1, 2, 2], 5) == 3;
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[..] == [3, 3, 3, 3];
    assert MaxDistEqualInRange([3, 3, 3, 3], 4) == 3;
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert a3[..] == [1, 2, 3, 4];
    assert MaxDistEqualInRange([1, 2, 3, 4], 4) == 0;
    assert d3 == 0; // a[i] to a[i]
}
