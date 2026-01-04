
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
  // Add helper assertions to prove the test outcome
  // Prove that all numbers 0..3 are in a1
  assert a1[0] == 0;
  assert a1[1] == 1;
  assert a1[2] == 2;
  assert a1[3] == 3;
  // Helper lemma to prove the postcondition for this specific case
  ghost var v1 := out1;
  assert v1 == 4;
  // Prove the second postcondition: forall x :: 0 <= x < v1 ==> exists k :: 0 <= k < |a1| && a1[k] == x
  // Since v1 = 4, we need to show for x=0,1,2,3
  assert exists k :: 0 <= k < |a1| && a1[k] == 0;
  assert exists k :: 0 <= k < |a1| && a1[k] == 1;
  assert exists k :: 0 <= k < |a1| && a1[k] == 2;
  assert exists k :: 0 <= k < |a1| && a1[k] == 3;
  // Prove the first postcondition: forall k :: 0 <= k < |a1| ==> a1[k] != v1
  assert a1[0] != 4;
  assert a1[1] != 4;
  assert a1[2] != 4;
  assert a1[3] != 4;
  assert out1 == 4;

  var a2: seq<int>:= [0, 1, 2, 2, 4, 9];
  assert a2[..] == [0, 1, 2, 2, 4, 9];
  var out2 := SmallestMissingNumber(a2);
  // Add helper assertions to prove the test outcome
  // Prove that all numbers 0..2 are in a2
  assert a2[0] == 0;
  assert a2[1] == 1;
  assert a2[2] == 2;
  assert a2[3] == 2;
  // Helper lemma for postconditions
  ghost var v2 := out2;
  assert v2 == 3;
  // Second postcondition: for x=0,1,2
  assert exists k :: 0 <= k < |a2| && a2[k] == 0;
  assert exists k :: 0 <= k < |a2| && a2[k] == 1;
  assert exists k :: 0 <= k < |a2| && a2[k] == 2;
  // First postcondition: all elements != 3
  assert a2[0] != 3;
  assert a2[1] != 3;
  assert a2[2] != 3;
  assert a2[3] != 3;
  assert a2[4] != 3;
  assert a2[5] != 3;
  assert out2 == 3;

  var a3: seq<int> := [2, 3, 5, 8, 9];
  assert a3[..] == [2, 3, 5, 8, 9];
  var out3 := SmallestMissingNumber(a3);
  // Add helper assertions to prove the test outcome
  // The quantifier for x in 0..0 is vacuously true
  // Second postcondition: forall x :: 0 <= x < 0 ==> ... is vacuously true
  // First postcondition: all elements != 0
  assert a3[0] != 0;
  assert a3[1] != 0;
  assert a3[2] != 0;
  assert a3[3] != 0;
  assert a3[4] != 0;
  assert out3 == 0;
}






