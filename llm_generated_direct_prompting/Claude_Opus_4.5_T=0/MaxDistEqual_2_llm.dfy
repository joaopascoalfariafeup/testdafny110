// Finds the maximum distance between equal elements in a non-empty array.

ghost function MaxDistEqualInRange<T(==)>(a: seq<T>, upToI: nat): nat
  requires upToI <= |a|
{
  if upToI == 0 then 0
  else 
    var i := upToI - 1;
    var maxFromI := MaxDistFromIndex(a, i);
    var prevMax := MaxDistEqualInRange(a, i);
    if maxFromI > prevMax then maxFromI else prevMax
}

ghost function MaxDistFromIndex<T(==)>(a: seq<T>, i: nat): nat
  requires i < |a|
{
  MaxDistFromIndexHelper(a, i, |a| - 1)
}

ghost function MaxDistFromIndexHelper<T(==)>(a: seq<T>, i: nat, j: nat): nat
  requires i < |a|
  requires j < |a|
{
  if j <= i then 0
  else if a[j] == a[i] then j - i
  else MaxDistFromIndexHelper(a, i, j - 1)
}

ghost predicate IsValidMaxDist<T(==)>(a: seq<T>, d: nat)
{
  (d == 0 || (exists i, j :: 0 <= i < j < |a| && j - i == d && a[i] == a[j])) &&
  (forall i, j :: 0 <= i < j < |a| && a[i] == a[j] ==> j - i <= d)
}

lemma MaxDistFromIndexHelperLemma<T(==)>(a: seq<T>, i: nat, j: nat, k: nat)
  requires i < |a|
  requires j < |a|
  requires i < k <= j
  requires a[k] == a[i]
  ensures MaxDistFromIndexHelper(a, i, j) >= k - i
{
  if j == k {
    assert a[j] == a[i];
  } else if a[j] == a[i] {
    assert j - i >= k - i;
  } else {
    MaxDistFromIndexHelperLemma(a, i, j - 1, k);
  }
}

lemma MaxDistFromIndexHelperUpperBound<T(==)>(a: seq<T>, i: nat, j: nat)
  requires i < |a|
  requires j < |a|
  ensures forall k :: i < k <= j && a[k] == a[i] ==> MaxDistFromIndexHelper(a, i, j) >= k - i
  ensures MaxDistFromIndexHelper(a, i, j) == 0 || (exists k :: i < k <= j && a[k] == a[i] && MaxDistFromIndexHelper(a, i, j) == k - i)
{
  if j <= i {
  } else if a[j] == a[i] {
  } else {
    MaxDistFromIndexHelperUpperBound(a, i, j - 1);
  }
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  ensures IsValidMaxDist(a[..], maxDist)
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant maxDist <= a.Length
    invariant maxDist == 0 || (exists i', j' :: 0 <= i' < j' < a.Length && j' - i' == maxDist && a[i'] == a[j'])
    invariant forall i', j' :: 0 <= i' < i && i' < j' < a.Length && a[i'] == a[j'] ==> j' - i' <= maxDist
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i as int <= j < a.Length
      invariant forall k :: j < k < a.Length && a[k] == a[i] ==> k - i <= maxDist
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
    assert a1[1] == a1[4] == 2;
    assert 4 - 1 == 3;
    assert d1 >= 3;
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[0] == a2[3] == 3;
    assert 3 - 0 == 3;
    assert d2 >= 3;
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert d3 == 0; // a[i] to a[i]
}
