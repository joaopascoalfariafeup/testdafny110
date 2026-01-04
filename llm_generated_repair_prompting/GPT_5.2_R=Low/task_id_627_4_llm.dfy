
ghost predicate SortedNondecreasing<T>(s: seq<T>, le: (T, T) -> bool)
{
  forall i, j :: 0 <= i < j < |s| ==> le(s[i], s[j])
}

ghost predicate SortedNat(s: seq<nat>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate SortedInt(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate AllNatInts(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> 0 <= s[i]
}

ghost predicate HasValuePrefixNat(s: seq<nat>, i: int, n: nat)
  requires 0 <= i <= |s|
{
  exists j :: 0 <= j < i && s[j] == n
}

ghost predicate HasValuePrefixInt(s: seq<int>, i: int, n: nat)
  requires 0 <= i <= |s|
{
  exists j :: 0 <= j < i && s[j] == n
}

lemma PrefixMonotoneNat(s: seq<nat>, i: int, ip: int, n: nat)
  requires 0 <= i <= ip <= |s|
  requires HasValuePrefixNat(s, i, n)
  ensures HasValuePrefixNat(s, ip, n)
{
  var j :| 0 <= j < i && s[j] == n;
  assert 0 <= j < ip && s[j] == n;
}

lemma PrefixMonotoneInt(s: seq<int>, i: int, ip: int, n: nat)
  requires 0 <= i <= ip <= |s|
  requires HasValuePrefixInt(s, i, n)
  ensures HasValuePrefixInt(s, ip, n)
{
  var j :| 0 <= j < i && s[j] == n;
  assert 0 <= j < ip && s[j] == n;
}

// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v' that is not present in the sequence.
method SmallestMissingNumberNat(s: seq<nat>) returns (v: nat)
  requires SortedNat(s)
  ensures (forall i :: 0 <= i < |s| ==> s[i] != v)
  ensures (forall n: nat :: n < v ==> HasValuePrefixNat(s, |s|, n))
{
  v := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant v <= i
    invariant (forall j :: 0 <= j < i ==> s[j] <= v)
    invariant (forall j :: 0 <= j < i ==> s[j] != v)
    invariant (forall n: nat :: n < v ==> HasValuePrefixNat(s, i, n))
  {
    var v0 := v;

    if s[i] == v {
      v := v + 1;
    }
    else if s[i] > v {
      assert forall j :: 0 <= j < i ==> s[j] != v;
      assert forall j :: i <= j < |s| ==> v < s[j] by {
        forall j | i <= j < |s| ensures v < s[j] {
          if j == i {
            assert v < s[i];
          } else {
            assert 0 <= i < j < |s|;
            assert s[i] <= s[j]; // by SortedNat(s)
            assert v < s[j];
          }
        }
      }
      return;
    }

    // Help prove the "all n < v are present" invariant for next iteration (i becomes i+1)
    if s[i] == v0 {
      assert HasValuePrefixNat(s, i + 1, v0); // witness j := i
    }
    forall n: nat | n < v ensures HasValuePrefixNat(s, i + 1, n) {
      if n < v0 {
        // from previous invariant at prefix i, extend to i+1
        PrefixMonotoneNat(s, i, i + 1, n);
      } else {
        // must be the newly-added value (only possible when v = v0+1)
        assert n == v0;
        assert HasValuePrefixNat(s, i + 1, v0);
      }
    }
  }
}

method SmallestMissingNumber(s: seq<int>) returns (v: nat)
  requires AllNatInts(s)
  requires SortedInt(s)
  ensures (forall i :: 0 <= i < |s| ==> s[i] != v)
  ensures (forall n: nat :: n < v ==> HasValuePrefixInt(s, |s|, n))
{
  v := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant v <= i
    invariant (forall j :: 0 <= j < i ==> s[j] <= v)
    invariant (forall j :: 0 <= j < i ==> s[j] != v)
    invariant (forall n: nat :: n < v ==> HasValuePrefixInt(s, i, n))
  {
    var v0 := v;

    if s[i] == v {
      v := v + 1;
    }
    else if s[i] > v {
      assert forall j :: 0 <= j < i ==> s[j] != v;
      assert forall j :: i <= j < |s| ==> v < s[j] by {
        forall j | i <= j < |s| ensures v < s[j] {
          if j == i {
            assert v < s[i];
          } else {
            assert 0 <= i < j < |s|;
            assert s[i] <= s[j]; // by SortedInt(s)
            assert v < s[j];
          }
        }
      }
      return;
    }

    // Help prove the "all n < v are present" invariant for next iteration (i becomes i+1)
    if s[i] == v0 {
      assert HasValuePrefixInt(s, i + 1, v0); // witness j := i
    }
    forall n: nat | n < v ensures HasValuePrefixInt(s, i + 1, n) {
      if n < v0 {
        PrefixMonotoneInt(s, i, i + 1, n);
      } else {
        assert n == v0;
        assert HasValuePrefixInt(s, i + 1, v0);
      }
    }
  }
}

// Test cases checked statically.
method SmallestMissingNumberTest() {
  var a1: seq<int> := [0, 1, 2, 3];
  assert AllNatInts(a1) && SortedInt(a1);
  var out1 := SmallestMissingNumber(a1);
  assert out1 == 4;

  var a2: seq<int>:= [0, 1, 2, 2, 4, 9];
  assert AllNatInts(a2) && SortedInt(a2);
  var out2 := SmallestMissingNumber(a2);
  assert out2 == 3;

  var a3: seq<int> := [2, 3, 5, 8, 9];
  assert AllNatInts(a3) && SortedInt(a3);
  var out3 := SmallestMissingNumber(a3);
  assert out3 == 0;
}

