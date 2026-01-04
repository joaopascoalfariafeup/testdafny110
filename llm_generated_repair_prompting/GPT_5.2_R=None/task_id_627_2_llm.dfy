
ghost predicate SortedNondecreasing(s: seq<nat>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
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
      invariant forall k: nat :: k < v ==> k in s[..i]
      invariant forall j :: 0 <= j < i ==> s[j] < v || v <= s[j]
    {
        if s[i] == v {
            v := v + 1;
        }
        else if s[i] > v {
            // establish postconditions for early return
            assert (forall k: nat :: k < v ==> k in s) by {
              // from invariant, membership in prefix implies membership in s
              assert forall k: nat :: k < v ==> k in s[..i];
            }
            assert v !in s by {
              // from invariant, for all seen elements either < v or >= v; combined with s[i] > v,
              // no element in prefix equals v; sortedness gives no later element can be v either
              assert forall j :: 0 <= j < i ==> s[j] != v;
              // show no index >= i can have value v, since s[i] > v and s is sorted
              assert forall j :: i <= j < |s| ==> s[j] != v by {
                forall j | i <= j < |s| {
                  // sortedness: s[i] <= s[j], and s[i] > v, so s[j] > v
                  assert s[i] <= s[j];
                  assert v < s[j];
                }
              }
              // combine to show v not in whole sequence
              assert forall j :: 0 <= j < |s| ==> s[j] != v;
            }
            return;
        }
        i := i + 1;
    }

    // loop finished: i == |s|
    assert forall k: nat :: k < v ==> k in s by {
      // invariant gives membership in whole prefix s[..|s|] == s
      assert forall k: nat :: k < v ==> k in s[..i];
      assert s[..i] == s;
    }

    assert v !in s by {
      // from invariant at i==|s|: all elements are either < v or >= v, hence none equals v
      assert forall j :: 0 <= j < i ==> s[j] < v || v <= s[j];
      assert forall j :: 0 <= j < |s| ==> s[j] != v by {
        forall j | 0 <= j < |s| {
          assert s[j] < v || v <= s[j];
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

