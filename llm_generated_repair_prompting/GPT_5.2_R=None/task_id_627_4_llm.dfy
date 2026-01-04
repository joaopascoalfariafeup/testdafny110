
ghost predicate SortedNondecreasing(s: seq<nat>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate AllBelowInPrefix(s: seq<nat>, i: int, v: nat)
{
  forall k: nat :: k < v ==> k in s[..i]
}

ghost predicate NoVInPrefix(s: seq<nat>, i: int, v: nat)
{
  forall j :: 0 <= j < i ==> s[j] != v
}

lemma PrefixMonotone(s: seq<nat>, i: int, j: int, k: nat)
  requires 0 <= i <= j <= |s|
  requires k in s[..i]
  ensures  k in s[..j]
{
  // since s[..i] is a prefix of s[..j]
  assert s[..j] == s[..i] + s[i..j];
  assert k in s[..i];
  assert k in s[..i] + s[i..j];
  assert k in s[..j];
}

lemma AllBelowStepWhenEqual(s: seq<nat>, i: int, v: nat)
  requires 0 <= i < |s|
  requires AllBelowInPrefix(s, i, v)
  requires s[i] == v
  ensures  AllBelowInPrefix(s, i+1, v+1)
{
  // show: forall k < v+1 ==> k in s[..i+1]
  assert s[..i+1] == s[..i] + [s[i]];
  forall k: nat | k < v+1
    ensures k in s[..i+1]
  {
    if k < v {
      assert k in s[..i];              // from AllBelowInPrefix(s,i,v)
      PrefixMonotone(s, i, i+1, k);    // lift membership to larger prefix
    } else {
      assert k == v;
      assert s[i] == k;
      assert k in [s[i]];
      assert k in s[..i] + [s[i]];
      assert k in s[..i+1];
    }
  }
}

lemma NoVFromSeparation(seen: seq<nat>, v: nat)
  requires forall j :: 0 <= j < |seen| ==> seen[j] < v || v <= seen[j]
  ensures  forall j :: 0 <= j < |seen| ==> seen[j] != v
{
  forall j | 0 <= j < |seen|
    ensures seen[j] != v
  {
    assert seen[j] < v || v <= seen[j];
    if seen[j] < v {
      assert seen[j] != v;
    } else {
      assert v <= seen[j];
      assert seen[j] != v;
    }
  }
}

lemma NoVInSuffixFromSorted(s: seq<nat>, i: int, v: nat)
  requires SortedNondecreasing(s)
  requires 0 <= i < |s|
  requires v < s[i]
  ensures  forall j :: i <= j < |s| ==> s[j] != v
{
  forall j | i <= j < |s|
    ensures s[j] != v
  {
    assert s[i] <= s[j];
    assert v < s[i];
    assert v < s[j];
    assert s[j] != v;
  }
}

// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence.
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires SortedNondecreasing(s)
  ensures forall k: nat :: k < v ==> k in s
  ensures v !in s
{
    v := 0;
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant 0 <= v <= i
      invariant AllBelowInPrefix(s, i, v)
      invariant forall j :: 0 <= j < i ==> s[j] < v || v <= s[j]
    {
        if s[i] == v {
            // maintain AllBelowInPrefix when v increases
            AllBelowStepWhenEqual(s, i, v);
            v := v + 1;
        }
        else if s[i] > v {
            // establish postconditions for early return
            assert (forall k: nat :: k < v ==> k in s) by {
              forall k: nat | k < v
                ensures k in s
              {
                assert k in s[..i]; // from invariant AllBelowInPrefix(s,i,v)
              }
            }

            assert v !in s by {
              // no v in prefix from separation invariant
              NoVFromSeparation(s[..i], v);
              assert NoVInPrefix(s, i, v);

              // no v in suffix from sortedness and s[i] > v
              NoVInSuffixFromSorted(s, i, v);

              // combine: no index has value v, thus v not in s
              assert forall j :: 0 <= j < |s| ==> s[j] != v by {
                forall j | 0 <= j < |s|
                  ensures s[j] != v
                {
                  if j < i {
                    assert s[j] != v; // from NoVInPrefix(s,i,v)
                  } else {
                    assert s[j] != v; // from NoVInSuffixFromSorted
                  }
                }
              }
            }
            return;
        }
        i := i + 1;
    }

    // loop finished: i == |s|
    assert forall k: nat :: k < v ==> k in s by {
      assert s[..i] == s;
      forall k: nat | k < v
        ensures k in s
      {
        assert k in s[..i]; // from AllBelowInPrefix
        assert k in s;
      }
    }

    assert v !in s by {
      // from separation invariant at i==|s|, no element equals v
      NoVFromSeparation(s[..i], v);
      assert forall j :: 0 <= j < |s| ==> s[j] != v by {
        assert s[..i] == s;
        forall j | 0 <= j < |s|
          ensures s[j] != v
        {
          assert s[j] != v;
        }
      }
    }
}


// Test cases checked statically.
method SmallestMissingNumberTest() {
  var a1: seq<int> := [0, 1, 2, 3];
  var out1 := SmallestMissingNumber(a1);
  assert out1 == 4;

  var a2: seq<int>:= [0, 1, 2, 2, 4, 9];
  var out2 := SmallestMissingNumber(a2);
  assert out2 == 3;

  var a3: seq<int> := [2, 3, 5, 8, 9];
  var out3 := SmallestMissingNumber(a3);
  assert out3 == 0;
}

