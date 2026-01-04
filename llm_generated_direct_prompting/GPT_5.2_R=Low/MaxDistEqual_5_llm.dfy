// Finds the maximum distance between equal elements in a non-empty array.

function MaxNat(x: nat, y: nat): nat {
  if x >= y then x else y
}

function MaxDistFromJ<T(==)>(s: seq<T>, i: nat, j: int): nat
  requires i < |s|
  decreases j
{
  if j < i then 0
  else if s[i] == s[j] then (j - i) as nat
  else MaxDistFromJ(s, i, j - 1)
}

function MaxDistFrom<T(==)>(s: seq<T>, i: nat): nat
  requires i < |s|
{
  MaxDistFromJ(s, i, |s| - 1)
}

function MaxDistRange<T(==)>(s: seq<T>, n: nat): nat
  requires n <= |s|
  decreases n
{
  if n == 0 then 0
  else MaxNat(MaxDistRange(s, n - 1), MaxDistFrom(s, n - 1))
}

function MaxDistEqualSeq<T(==)>(s: seq<T>): nat {
  MaxDistRange(s, |s|)
}

lemma MaxDistFromJ_UpperBound<T(==)>(s: seq<T>, i: nat, j: int, bd: nat)
  requires i < |s|
  requires j < |s|
  requires j <= i + bd
  ensures MaxDistFromJ(s, i, j) <= bd
  decreases j
{
  if j < i {
  } else {
    if s[i] == s[j] {
      assert (j - i) as nat <= bd;
    } else {
      MaxDistFromJ_UpperBound(s, i, j - 1, bd);
    }
  }
}

lemma MaxDistFromJ_NoMatchBeyondTop<T(==)>(s: seq<T>, i: nat, limit: int, top: int)
  requires i < |s|
  requires -1 <= limit <= top < |s|
  requires forall k :: limit < k <= top ==> s[i] != s[k]
  ensures MaxDistFromJ(s, i, top) == MaxDistFromJ(s, i, limit)
  decreases top
{
  if top == limit {
  } else if top < i {
    assert limit < i;
  } else {
    assert s[i] != s[top];
    MaxDistFromJ_NoMatchBeyondTop(s, i, limit, top - 1);
  }
}

lemma MaxDistFrom_MaxIndex<T(==)>(s: seq<T>, i: nat, j: int)
  requires i < |s|
  requires i <= j < |s|
  requires s[i] == s[j]
  requires forall k :: j < k < |s| ==> s[i] != s[k]
  ensures MaxDistFrom(s, i) == (j - i) as nat
{
  assert forall k :: j < k <= |s| - 1 ==> s[i] != s[k];
  MaxDistFromJ_NoMatchBeyondTop(s, i, j, |s| - 1);
  assert MaxDistFrom(s, i) == MaxDistFromJ(s, i, j);
}

method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist == MaxDistEqualSeq(a[..])
  ensures maxDist <= a.Length - 1
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant maxDist == MaxDistRange(a[..], i as nat)
  {
    ghost var prev := maxDist;

    var j := a.Length - 1;
    while j > i + maxDist
      invariant 0 <= i < a.Length
      invariant -1 <= j < a.Length
      invariant maxDist == prev
      invariant forall k :: j < k < a.Length ==> a[k] != a[i]
      decreases j
    {
      if (a[j] == a[i]) {
        assert 0 <= i <= j;
        maxDist := (j - i) as nat;
        break;
      }
      j := j - 1;    
    }

    if maxDist == prev {
      assert j <= i + prev;
      assert forall k :: j < k < a.Length ==> a[k] != a[i];
      if i <= j {
        assert forall k :: j < k <= a.Length - 1 ==> a[i] != a[k];
        MaxDistFromJ_NoMatchBeyondTop(a[..], i as nat, j, a.Length - 1);
        MaxDistFromJ_UpperBound(a[..], i as nat, j, prev);
      } else {
        assert MaxDistFrom(a[..], i as nat) == 0;
      }
      assert MaxNat(prev, MaxDistFrom(a[..], i as nat)) == prev;
    } else {
      assert a[j] == a[i];
      assert forall k :: j < k < a.Length ==> a[k] != a[i];
      MaxDistFrom_MaxIndex(a[..], i as nat, j);
      assert maxDist == MaxDistFrom(a[..], i as nat);
      assert prev < maxDist;
      assert MaxNat(prev, MaxDistFrom(a[..], i as nat)) == maxDist;
    }

    assert maxDist == MaxNat(prev, MaxDistFrom(a[..], i as nat));
    assert maxDist == MaxNat(MaxDistRange(a[..], i as nat), MaxDistFrom(a[..], i as nat));
    assert maxDist == MaxDistRange(a[..], (i + 1) as nat);
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
