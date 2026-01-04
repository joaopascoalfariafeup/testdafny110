
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

// Witness helpers (needed in tests; SMT typically won't guess the existential witness)
lemma HasValuePrefixNatWitness(s: seq<nat>, i: int, j: int, n: nat)
  requires 0 <= j < i <= |s|
  requires s[j] == n
  ensures HasValuePrefixNat(s, i, n)
{
  assert HasValuePrefixNat(s, i, n) by {
    assert 0 <= j < i;
    assert s[j] == n;
  }
}

lemma HasValuePrefixIntWitness(s: seq<int>, i: int, j: int, n: nat)
  requires 0 <= j < i <= |s|
  requires s[j] == n
  ensures HasValuePrefixInt(s, i, n)
{
  assert HasValuePrefixInt(s, i, n) by {
    assert 0 <= j < i;
    assert s[j] == n;
  }
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

lemma NotHasValueFromAllNeqInt(s: seq<int>, i: int, n: nat)
  requires 0 <= i <= |s|
  requires forall k :: 0 <= k < i ==> s[k] != n
  ensures !HasValuePrefixInt(s, i, n)
{
  if HasValuePrefixInt(s, i, n) {
    var j :| 0 <= j < i && s[j] == n;
    assert s[j] != n;
  }
}

lemma LowerBoundFromMissingInt(s: seq<int>, v: nat, n: nat)
  requires (forall i :: 0 <= i < |s| ==> s[i] != v)
  requires (forall m: nat :: m < v ==> HasValuePrefixInt(s, |s|, m))
  requires !HasValuePrefixInt(s, |s|, n)
  ensures v <= n
{
  if n < v {
    assert HasValuePrefixInt(s, |s|, n);
  }
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

      // Prove postconditions on this early-return path
      assert forall j :: 0 <= j < |s| ==> s[j] != v by {
        forall j | 0 <= j < |s| ensures s[j] != v {
          if j < i {
            assert s[j] != v;
          } else {
            assert i <= j < |s|;
            assert v < s[j];
            assert s[j] != v;
          }
        }
      }
      assert forall n: nat :: n < v ==> HasValuePrefixNat(s, |s|, n) by {
        forall n: nat | n < v ensures HasValuePrefixNat(s, |s|, n) {
          PrefixMonotoneNat(s, i, |s|, n);
        }
      }
      return;
    }

    // Help prove the "all n < v are present" invariant for next iteration (i becomes i+1)
    if s[i] == v0 {
      assert HasValuePrefixNat(s, i + 1, v0); // witness j := i
    }
    forall n: nat {:trigger HasValuePrefixNat(s, i + 1, n)} | n < v ensures HasValuePrefixNat(s, i + 1, n) {
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

      // Prove postconditions on this early-return path
      assert forall j :: 0 <= j < |s| ==> s[j] != v by {
        forall j | 0 <= j < |s| ensures s[j] != v {
          if j < i {
            assert s[j] != v;
          } else {
            assert i <= j < |s|;
            assert v < s[j];
            assert s[j] != v;
          }
        }
      }
      assert forall n: nat :: n < v ==> HasValuePrefixInt(s, |s|, n) by {
        forall n: nat | n < v ensures HasValuePrefixInt(s, |s|, n) {
          PrefixMonotoneInt(s, i, |s|, n);
        }
      }
      return;
    }

    // Help prove the "all n < v are present" invariant for next iteration (i becomes i+1)
    if s[i] == v0 {
      assert HasValuePrefixInt(s, i + 1, v0); // witness j := i
    }
    forall n: nat {:trigger HasValuePrefixInt(s, i + 1, n)} | n < v ensures HasValuePrefixInt(s, i + 1, n) {
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
  assert a1 == [0, 1, 2, 3];
  assert AllNatInts(a1) && SortedInt(a1);
  var out1 := SmallestMissingNumber(a1);

  // out1 >= 4 (since 0..3 are present, out1 cannot be any of them)
  assert a1[0] == 0 && a1[1] == 1 && a1[2] == 2 && a1[3] == 3;
  assert HasValuePrefixInt(a1, |a1|, 0) by { HasValuePrefixIntWitness(a1, |a1|, 0, 0); }
  assert HasValuePrefixInt(a1, |a1|, 1) by { HasValuePrefixIntWitness(a1, |a1|, 1, 1); }
  assert HasValuePrefixInt(a1, |a1|, 2) by { HasValuePrefixIntWitness(a1, |a1|, 2, 2); }
  assert HasValuePrefixInt(a1, |a1|, 3) by { HasValuePrefixIntWitness(a1, |a1|, 3, 3); }
  assert out1 != 0 && out1 != 1 && out1 != 2 && out1 != 3 by {
    if out1 == 0 {
      var j :| 0 <= j < |a1| && a1[j] == 0;
      assert a1[j] != out1;
    }
    if out1 == 1 {
      var j :| 0 <= j < |a1| && a1[j] == 1;
      assert a1[j] != out1;
    }
    if out1 == 2 {
      var j :| 0 <= j < |a1| && a1[j] == 2;
      assert a1[j] != out1;
    }
    if out1 == 3 {
      var j :| 0 <= j < |a1| && a1[j] == 3;
      assert a1[j] != out1;
    }
  }
  assert 4 <= out1;

  // out1 <= 4 (since 4 is missing)
  assert forall i :: 0 <= i < |a1| ==> a1[i] != 4;
  assert !HasValuePrefixInt(a1, |a1|, 4) by {
    NotHasValueFromAllNeqInt(a1, |a1|, 4);
  }
  LowerBoundFromMissingInt(a1, out1, 4);
  assert out1 <= 4;

  assert out1 == 4;

  var a2: seq<int>:= [0, 1, 2, 2, 4, 9];
  assert a2 == [0, 1, 2, 2, 4, 9];
  assert AllNatInts(a2) && SortedInt(a2);
  var out2 := SmallestMissingNumber(a2);

  // out2 >= 3 (0..2 are present)
  assert a2[0] == 0 && a2[1] == 1 && a2[2] == 2;
  assert HasValuePrefixInt(a2, |a2|, 0) by { HasValuePrefixIntWitness(a2, |a2|, 0, 0); }
  assert HasValuePrefixInt(a2, |a2|, 1) by { HasValuePrefixIntWitness(a2, |a2|, 1, 1); }
  assert HasValuePrefixInt(a2, |a2|, 2) by { HasValuePrefixIntWitness(a2, |a2|, 2, 2); }
  assert out2 != 0 && out2 != 1 && out2 != 2 by {
    if out2 == 0 {
      var j :| 0 <= j < |a2| && a2[j] == 0;
      assert a2[j] != out2;
    }
    if out2 == 1 {
      var j :| 0 <= j < |a2| && a2[j] == 1;
      assert a2[j] != out2;
    }
    if out2 == 2 {
      var j :| 0 <= j < |a2| && a2[j] == 2;
      assert a2[j] != out2;
    }
  }
  assert 3 <= out2;

  // out2 <= 3 (since 3 is missing)
  assert forall i :: 0 <= i < |a2| ==> a2[i] != 3;
  assert !HasValuePrefixInt(a2, |a2|, 3) by {
    NotHasValueFromAllNeqInt(a2, |a2|, 3);
  }
  LowerBoundFromMissingInt(a2, out2, 3);
  assert out2 <= 3;

  assert out2 == 3;

  var a3: seq<int> := [2, 3, 5, 8, 9];
  assert a3 == [2, 3, 5, 8, 9];
  assert AllNatInts(a3) && SortedInt(a3);
  var out3 := SmallestMissingNumber(a3);

  // out3 <= 0 (since 0 is missing) and out3 is nat, so out3 == 0
  assert forall i :: 0 <= i < |a3| ==> a3[i] != 0;
  assert !HasValuePrefixInt(a3, |a3|, 0) by {
    NotHasValueFromAllNeqInt(a3, |a3|, 0);
  }
  LowerBoundFromMissingInt(a3, out3, 0);
  assert out3 <= 0;
  assert out3 == 0;
}

