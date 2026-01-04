
ghost predicate SortedNatSeq(s: seq<nat>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate MissingUpTo(s: seq<nat>, n: nat)
{
  forall k: nat :: k < n ==> exists i :: 0 <= i < |s| && s[i] == k
}

ghost predicate NotPresent(s: seq<nat>, x: nat)
{
  forall i :: 0 <= i < |s| ==> s[i] != x
}

// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires SortedNatSeq(s)
  ensures NotPresent(s, v)
  ensures MissingUpTo(s, v)
{
    v := 0; 
    for i := 0 to |s|
      invariant 0 <= v <= i
      invariant MissingUpTo(s[..i], v)
      invariant NotPresent(s[..i], v)
      invariant SortedNatSeq(s)
    {
        if s[i] == v {
            v := v + 1;
        }
        else if s[i] > v {
            return;
        }
        assert MissingUpTo(s[..i+1], v);
        assert NotPresent(s[..i+1], v);
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

