// Finds the maximum distance between equal elements in a non-empty array.

ghost function {:fuel 5} MaxDistEqualInRange<T(==)>(a: seq<T>, upToI: nat): nat
{
  if upToI == 0 then 0
  else 
    var i := upToI - 1;
    var maxPrev := MaxDistEqualInRange(a, i);
    var maxForI := MaxDistFromI(a, i, |a| - 1);
    if maxForI > maxPrev then maxForI else maxPrev
}

ghost function {:fuel 5} MaxDistFromI<T(==)>(a: seq<T>, i: nat, j: int): nat
  requires -1 <= j < |a|
{
  if j <= i then 0
  else if a[j] == a[i] then j - i
  else MaxDistFromI(a, i, j - 1)
}



lemma MaxDistFromIBound<T(==)>(a: seq<T>, i: nat, j: int)
  requires -1 <= j < |a|
  ensures MaxDistFromI(a, i, j) <= (if j <= i then 0 else j - i)
{
  if j <= i {
  } else if a[j] == a[i] {
  } else {
    MaxDistFromIBound(a, i, j - 1);
  }
}


method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  ensures maxDist == MaxDistEqualInRange(a[..], a.Length)
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant maxDist == MaxDistEqualInRange(a[..], i)
  {
    var maxDistOld := maxDist;
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i <= j < a.Length || j == i - 1 || j == i + maxDist as int
      invariant maxDist == maxDistOld ==> MaxDistFromI(a[..], i, a.Length - 1) == MaxDistFromI(a[..], i, j)
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
        break;
      }
      j := j - 1;    
    }
    if maxDist == maxDistOld {
      MaxDistFromIBound(a[..], i, j);
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