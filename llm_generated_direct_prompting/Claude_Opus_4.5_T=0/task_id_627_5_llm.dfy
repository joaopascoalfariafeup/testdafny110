
// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall k :: 0 <= k < v ==> k in s
  ensures v !in s
{
    v := 0; 
    for i := 0 to |s|
      invariant forall k :: 0 <= k < v ==> k in s[..i]
      invariant v <= i
      invariant forall k :: 0 <= k < i ==> s[k] < v || s[k] >= v
      invariant v !in s[..i]
    {
        if s[i] == v {
            v := v + 1;
        }
        else if s[i] > v {
            assert v !in s[..i];
            assert s[i] > v;
            assert forall j :: i <= j < |s| ==> s[j] >= s[i] > v;
            assert v !in s[i..];
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

