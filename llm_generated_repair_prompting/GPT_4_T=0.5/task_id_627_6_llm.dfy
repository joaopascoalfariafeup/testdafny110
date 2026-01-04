
// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v' that is not present in the sequence. 

ghost predicate p(s: seq<nat>, i: nat, v: nat) 
  { exists j :: 0 <= j < |s| && s[j] == i && i < v }

method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j] // 's' is sorted in strictly increasing order
  ensures v >= 0
  ensures forall i :: 0 <= i < |s| ==> s[i] != v // 'v' is not present in 's'
  ensures forall i :: 0 <= i < v ==> p(s, i, v) // 'v' is the smallest number not present in 's'
{
    v := 0; 
    for i := 0 to |s|
      invariant 0 <= v <= i+1 // 'v' is within the range [0, i+1)
      invariant forall j :: 0 <= j < i ==> s[j] != v // 'v' is not present in the first 'i' elements of 's'
      invariant forall j :: 0 <= j < v ==> p(s[..i], j, v) // 'v' is the smallest number not present in the first 'i' elements of 's'
      invariant i <= |s| // 'i' is always less than or equal to the length of 's'
    {
        if i < |s| && s[i] == v {
            v := v + 1;
        }
        else if i < |s| && s[i] > v {
            return;
        }
    }
}

// Test cases checked statically.
method SmallestMissingNumberTest() {
  var a1: seq<int> := [0, 1, 2, 3];
  var out1 := SmallestMissingNumber(a1);
  assert forall i :: 0 <= i < out1 ==> p(a1, i, out1); // helper for the test assertion
  assert out1 == 4;

  var a2: seq<int>:= [0, 1, 2, 4, 9];
  var out2 := SmallestMissingNumber(a2);
  assert forall i :: 0 <= i < out2 ==> p(a2, i, out2); // helper for the test assertion
  assert out2 == 3;

  var a3: seq<int> := [2, 3, 5, 8, 9];
  var out3 := SmallestMissingNumber(a3);
  assert forall i :: 0 <= i < out3 ==> p(a3, i, out3); // helper for the test assertion
  assert out3 == 0;
}


