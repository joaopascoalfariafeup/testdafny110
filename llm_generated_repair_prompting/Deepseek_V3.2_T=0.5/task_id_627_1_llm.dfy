
// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
{
    v := 0; 
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant v >= 0
      invariant forall k :: 0 <= k < i ==> s[k] != v
      invariant forall k :: 0 <= k < i ==> s[k] < v ==> (exists l :: 0 <= l < i && s[l] == s[k] + 1)
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

