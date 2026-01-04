
// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures v !in s
    ensures forall k: nat :: k < v ==> k in s
{
    v := 0; 
    for i := 0 to |s|
        invariant v !in s[..i]
        invariant forall k: nat :: k < v ==> k in s
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
  assert 4 !in a1;
  assert out1 == 4;

  var a2: seq<int>:= [0, 1, 2, 2, 4, 9];
  var out2 := SmallestMissingNumber(a2);
  assert 3 !in a2;
  assert out2 == 3;

  var a3: seq<int> := [2, 3, 5, 8, 9];
  var out3 := SmallestMissingNumber(a3);
  assert 0 !in a3;
  assert out3 == 0;
}