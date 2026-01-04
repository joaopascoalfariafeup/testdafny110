
// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall k :: 0 <= k < v ==> k in s
  ensures v !in s
{
    v := 0; 
    for i := 0 to |s|
      invariant forall k :: 0 <= k < v ==> k in s
      invariant v !in s[..i]
      invariant v <= i
    {
        if s[i] == v {
            v := v + 1;
        }
        else if s[i] > v {
            // Since s is sorted and s[i] > v, v cannot be in s[i..]
            assert forall j :: i <= j < |s| ==> s[j] >= s[i] > v;
            assert v !in s[i..];
            assert v !in s[..i];
            assert s == s[..i] + s[i..];
            assert v !in s;
            return;
        }
    }
}

// Helper lemma to prove uniqueness of result
lemma SmallestMissingUnique(s: seq<nat>, v: nat)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall k :: 0 <= k < v ==> k in s
  requires v !in s
  ensures forall u: nat :: (forall k :: 0 <= k < u ==> k in s) && u !in s ==> u == v
{
  forall u: nat | (forall k :: 0 <= k < u ==> k in s) && u !in s
    ensures u == v
  {
    if u < v {
      assert u in s; // contradiction since u !in s
    } else if u > v {
      assert v < u;
      assert v in s; // contradiction since v !in s
    }
  }
}

// Test cases checked statically.
method SmallestMissingNumberTest() {
  var a1: seq<int> := [0, 1, 2, 3];
  var out1 := SmallestMissingNumber(a1);
  assert 0 in a1 && 1 in a1 && 2 in a1 && 3 in a1;
  assert 4 !in a1;
  SmallestMissingUnique(a1, 4);
  assert out1 == 4;

  var a2: seq<int>:= [0, 1, 2, 2, 4, 9];
  var out2 := SmallestMissingNumber(a2);
  assert 0 in a2 && 1 in a2 && 2 in a2;
  assert 3 !in a2;
  SmallestMissingUnique(a2, 3);
  assert out2 == 3;

  var a3: seq<int> := [2, 3, 5, 8, 9];
  var out3 := SmallestMissingNumber(a3);
  assert 0 !in a3;
  SmallestMissingUnique(a3, 0);
  assert out3 == 0;
}


