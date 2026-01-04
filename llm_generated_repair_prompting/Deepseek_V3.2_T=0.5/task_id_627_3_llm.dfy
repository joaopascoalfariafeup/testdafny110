
// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
  ensures forall k :: 0 <= k < |s| ==> s[k] != v
  ensures forall x :: 0 <= x < v ==> exists k :: 0 <= k < |s| && s[k] == x
{
    v := 0; 
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant v >= 0
      invariant forall k :: 0 <= k < i ==> s[k] != v
      invariant forall x :: 0 <= x < v ==> exists k :: 0 <= k < i && s[k] == x
      invariant forall k :: 0 <= k < i ==> s[k] <= v
    {
        if s[i] == v {
            v := v + 1;
        }
        else if s[i] > v {
            return;
        }
        i := i + 1;
    }
}


// Test cases checked statically.
method SmallestMissingNumberTest() {
  var a1: seq<int> := [0, 1, 2, 3];
  assert a1[..] == [0, 1, 2, 3];
  var out1 := SmallestMissingNumber(a1);
  assert out1 == 4;

  var a2: seq<int>:= [0, 1, 2, 2, 4, 9];
  assert a2[..] == [0, 1, 2, 2, 4, 9];
  var out2 := SmallestMissingNumber(a2);
  assert out2 == 3;

  var a3: seq<int> := [2, 3, 5, 8, 9];
  assert a3[..] == [2, 3, 5, 8, 9];
  var out3 := SmallestMissingNumber(a3);
  assert out3 == 0;
}


