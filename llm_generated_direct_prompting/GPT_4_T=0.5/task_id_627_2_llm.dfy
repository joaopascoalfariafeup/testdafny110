
// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]  // 's' is sorted
{
    v := 0; 
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant forall k :: 0 <= k < i ==> s[k] <= v
      invariant v == i ==> forall k :: 0 <= k < i ==> s[k] == k
      invariant v < i ==> exists k :: 0 <= k < i && s[k] != k
    {
        if s[i] == v {
            v := v + 1;
        }
        else if s[i] > v {
            return;
        }
    }
    ensures (v == |s| ==> forall k :: 0 <= k < |s| ==> s[k] == k) &&
            (v < |s| ==> exists k :: 0 <= k < |s| && s[k] != k)
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

