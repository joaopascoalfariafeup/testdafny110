// Finds the maximum distance between equal elements in a non-empty array.

ghost function {:fuel 5} MaxDistEqualInRange<T(==)>(a: seq<T>, upToI: nat): nat
  requires upToI <= |a|
{
  if upToI == 0 then 0
  else 
    var i := upToI - 1;
    var maxPrev := MaxDistEqualInRange(a, i);
    var maxForI := MaxDistFromI(a, i, |a| - 1);
    if maxForI > maxPrev then maxForI else maxPrev
}

ghost function {:fuel 5} MaxDistFromI<T(==)>(a: seq<T>, i: nat, j: int): nat
  requires i < |a|
  requires -1 <= j < |a|
{
  if j <= i then 0
  else if a[j] == a[i] then j - i
  else MaxDistFromI(a, i, j - 1)
}

ghost predicate IsMaxDistEqual<T(==)>(a: seq<T>, d: nat)
{
  // d is achievable: either d == 0, or there exist indices with distance d and equal elements
  (d == 0 || exists i, j :: 0 <= i < j < |a| && j - i == d && a[i] == a[j])
  &&
  // d is maximal: no larger distance exists
  (forall i, j :: 0 <= i < j < |a| && a[i] == a[j] ==> j - i <= d)
}

lemma MaxDistFromICorrect<T(==)>(a: seq<T>, i: nat, j: int)
  requires i < |a|
  requires -1 <= j < |a|
  ensures var d := MaxDistFromI(a, i, j);
          (d == 0 || (i < d + i <= j && a[i] == a[d + i]))
          && (forall k :: i < k <= j && a[i] == a[k] ==> k - i <= d)
{
  if j <= i {
  } else if a[j] == a[i] {
  } else {
    MaxDistFromICorrect(a, i, j - 1);
  }
}

lemma MaxDistEqualInRangeCorrect<T(==)>(a: seq<T>, upToI: nat)
  requires upToI <= |a|
  ensures var d := MaxDistEqualInRange(a, upToI);
          (d == 0 || exists i, j :: 0 <= i < upToI && i < j < |a| && j - i == d && a[i] == a[j])
          && (forall i, j :: 0 <= i < upToI && i < j < |a| && a[i] == a[j] ==> j - i <= d)
{
  if upToI == 0 {
  } else {
    var i := upToI - 1;
    MaxDistEqualInRangeCorrect(a, i);
    MaxDistFromICorrect(a, i, |a| - 1);
  }
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  ensures maxDist == MaxDistEqualInRange(a[..], a.Length)
  ensures IsMaxDistEqual(a[..], maxDist)
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant maxDist == MaxDistEqualInRange(a[..], i)
  {
    var maxDistOld := maxDist;
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i <= j < a.Length || j == i - 1
      invariant maxDist >= maxDistOld
      invariant MaxDistFromI(a[..], i, a.Length - 1) <= maxDist || MaxDistFromI(a[..], i, a.Length - 1) == MaxDistFromI(a[..], i, j)
      invariant maxDist == maxDistOld || (maxDist == j + 1 - i && a[i] == a[j + 1])
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
        break;
      }
      j := j - 1;    
    }
    assert maxDist >= MaxDistFromI(a[..], i, a.Length - 1);
    assert maxDist >= maxDistOld;
  }
  MaxDistEqualInRangeCorrect(a[..], a.Length);
}

method testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    var d1 := MaxDistEqual(a1);
    assert a1[..] == [1, 2, 1, 2, 2];
    assert MaxDistFromI(a1[..], 0, 4) == 2;
    assert MaxDistFromI(a1[..], 1, 4) == 3;
    assert MaxDistEqualInRange(a1[..], 2) == 3;
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[..] == [3, 3, 3, 3];
    assert MaxDistFromI(a2[..], 0, 3) == 3;
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert a3[..] == [1, 2, 3, 4];
    assert d3 == 0; // a[i] to a[i]
}
