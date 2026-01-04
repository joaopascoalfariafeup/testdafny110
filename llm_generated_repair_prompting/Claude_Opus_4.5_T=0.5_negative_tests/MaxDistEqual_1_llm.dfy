// Finds the maximum distance between equal elements in a non-empty array.
ghost function MaxDistEqualFunc<T(==)>(a: seq<T>, i: nat, j: nat): nat
  requires i <= j <= |a|
  decreases j - i
{
  if i >= j then 0
  else if a[i] == a[j-1] then j - 1 - i
  else MaxDistEqualFunc(a, i, j-1)
}

ghost function MaxDistUpTo<T(==)>(a: seq<T>, n: nat): nat
  requires n <= |a|
  decreases n
{
  if n == 0 then 0
  else 
    var prevMax := MaxDistUpTo(a, n-1);
    var currMax := MaxDistEqualFunc(a, n-1, |a|);
    if currMax > prevMax then currMax else prevMax
}

ghost predicate ValidMaxDist<T(==)>(a: seq<T>, d: nat)
{
  (d == 0 || (exists i, j :: 0 <= i < j < |a| && j - i == d && a[i] == a[j])) &&
  (forall i, j :: 0 <= i < j < |a| && a[i] == a[j] ==> j - i <= d)
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures ValidMaxDist(a[..], maxDist)
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= maxDist <= a.Length - 1
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
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[0] == a2[3] == 3;
    assert 3 - 0 == 3;
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert forall i, j :: 0 <= i < j < 4 ==> a3[i] != a3[j];
    assert d3 == 0; // a[i] to a[i]

    // empty array case
    var a4 := new int[] []; 
    //@invalid var d4 := MaxDistEqual(a4); // should not verify due to precondition violation
}
