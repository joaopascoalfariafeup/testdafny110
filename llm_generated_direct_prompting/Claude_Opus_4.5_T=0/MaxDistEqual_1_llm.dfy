// Finds the maximum distance between equal elements in a non-empty array.
ghost function MaxDistEqualInSeq<T(==)>(s: seq<T>): nat
{
  if |s| == 0 then 0
  else 
    var lastIdx := |s| - 1;
    var distFromLast := if s[lastIdx] in s[..lastIdx] then 
                          lastIdx - FindFirstIndex(s[..lastIdx], s[lastIdx])
                        else 0;
    var distInPrefix := MaxDistEqualInSeq(s[..lastIdx]);
    if distFromLast > distInPrefix then distFromLast else distInPrefix
}

ghost function FindFirstIndex<T(==)>(s: seq<T>, x: T): nat
  requires x in s
  ensures FindFirstIndex(s, x) < |s|
  ensures s[FindFirstIndex(s, x)] == x
  ensures forall k :: 0 <= k < FindFirstIndex(s, x) ==> s[k] != x
{
  if s[0] == x then 0 else 1 + FindFirstIndex(s[1..], x)
}

ghost predicate HasPairWithDist<T(==)>(s: seq<T>, d: nat)
{
  exists i, j :: 0 <= i < j < |s| && j - i == d && s[i] == s[j]
}

ghost predicate IsMaxDistEqual<T(==)>(s: seq<T>, d: nat)
{
  (d == 0 || HasPairWithDist(s, d)) &&
  (forall i, j :: 0 <= i < j < |s| && s[i] == s[j] ==> j - i <= d)
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  ensures IsMaxDistEqual(a[..], maxDist)
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= maxDist <= a.Length
    invariant forall p, q :: 0 <= p < i && p < q < a.Length && a[p] == a[q] ==> q - p <= maxDist
    invariant maxDist == 0 || HasPairWithDist(a[..], maxDist)
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i <= j < a.Length || j == i - 1
      invariant i + maxDist <= j || j == i + maxDist - 1 || (j >= i && a[j+1] == a[i] && j + 1 - i > maxDist)
      invariant forall k :: j < k < a.Length ==> (k > i + maxDist ==> a[k] != a[i])
      invariant 0 <= maxDist <= a.Length
      invariant forall p, q :: 0 <= p < i && p < q < a.Length && a[p] == a[q] ==> q - p <= maxDist
      invariant maxDist == 0 || HasPairWithDist(a[..], maxDist)
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
        break;
      }
      j := j - 1;    
    }
  }
}

method {:fuel IsMaxDistEqual, 6} {:fuel HasPairWithDist, 6} testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    var d1 := MaxDistEqual(a1);
    assert a1[1] == a1[4];
    assert HasPairWithDist(a1[..], 3);
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[0] == a2[3];
    assert HasPairWithDist(a2[..], 3);
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert d3 == 0; // a[i] to a[i]
}
