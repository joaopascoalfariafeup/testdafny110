
predicate SortedNondecreasing(s: seq<nat>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate Contains(s: seq<nat>, x: nat)
{
  exists i :: 0 <= i < |s| && s[i] == x
}

predicate ContainsPrefix(s: seq<nat>, x: nat, n: nat)
{
  exists i :: 0 <= i < n && i < |s| && s[i] == x
}

// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires SortedNondecreasing(s)
  ensures !Contains(s, v)
  ensures forall k: nat :: k < v ==> Contains(s, k)
{
    v := 0; 
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant SortedNondecreasing(s)
      invariant v <= i
      invariant forall j :: 0 <= j < i ==> s[j] < v
      invariant forall k: nat :: k < v ==> ContainsPrefix(s, k, i)
    {
        if s[i] == v {
            v := v + 1;
        }
        else if s[i] > v {
            assert forall j :: 0 <= j < i ==> s[j] != v;
            assert forall j :: i <= j < |s| ==> s[i] <= s[j];
            assert forall j :: i <= j < |s| ==> v < s[j];
            assert forall j :: i <= j < |s| ==> s[j] != v;
            assert forall j :: 0 <= j < |s| ==> s[j] != v;
            assert !Contains(s, v);
            assert forall k: nat :: k < v ==> Contains(s, k);
            return;
        }
    }
    assert forall j :: 0 <= j < |s| ==> s[j] < v;
    assert !Contains(s, v);
    assert forall k: nat :: k < v ==> Contains(s, k);
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

