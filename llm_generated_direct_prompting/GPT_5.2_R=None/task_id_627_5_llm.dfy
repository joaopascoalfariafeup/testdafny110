
ghost predicate SortedNatSeq(s: seq<nat>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate MissingFromPrefix(s: seq<nat>, n: int, v: nat)
{
  forall k :: 0 <= k < n ==> s[k] != v
}

ghost predicate AllBelowPresentInPrefix(s: seq<nat>, n: int, v: nat)
{
  forall u: nat :: u < v ==> (exists k :: 0 <= k < n && s[k] == u)
}

// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires SortedNatSeq(s)
  ensures MissingFromPrefix(s, |s|, v)
  ensures forall u: nat :: u < v ==> (exists k :: 0 <= k < |s| && s[k] == u)
{
    v := 0; 
    for i := 0 to |s|
      invariant 0 <= v <= i
      invariant forall u: nat :: u < v ==> (exists k :: 0 <= k < i && s[k] == u)
      invariant MissingFromPrefix(s, i, v)
    {
        if s[i] == v {
            v := v + 1;
        }
        else if s[i] > v {
            return;
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

