
// Given a sorted sequence 's' of natural numbers,
// finds the smallest natural number 'v that is not present in the sequence. 
method SmallestMissingNumber(s: seq<nat>) returns (v: nat)
  requires forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
  ensures forall k :: 0 <= k < |s| ==> s[k] != v
  ensures forall x :: 0 <= x < v ==> exists k :: 0 <= k < |s| && s[k] == x
  ensures v <= |s|
{
    v := 0; 
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant v >= 0
      invariant forall k :: 0 <= k < i ==> s[k] != v
      invariant forall x :: 0 <= x < v ==> exists k :: 0 <= k < i && s[k] == x
      invariant forall k :: 0 <= k < i ==> s[k] <= v
      invariant v <= i
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
  // The following assertion is not provable from the postconditions alone
  // because the postconditions don't guarantee v == 4 for this input.
  // We need to add additional postconditions to the method.
  // Instead, we'll prove the test outcome using the postconditions directly.
  // First postcondition: all elements != out1
  // Second postcondition: all x < out1 appear in a1
  // For a1 = [0,1,2,3], we know 0,1,2,3 appear, so out1 must be at least 4.
  // Also, 4 does not appear, so out1 could be 4.
  // But we need to show it's exactly 4.
  // We'll add a lemma: if v is a candidate satisfying the postconditions,
  // and v' < v, then v' cannot satisfy the second postcondition.
  // Actually, we can prove by contradiction:
  // Suppose out1 < 4. Then out1 is 0,1,2, or 3.
  // But each of these appears in a1, violating first postcondition.
  // So out1 >= 4.
  // Also, 4 does not appear, so out1 = 4 satisfies first postcondition.
  // And for all x < 4, x appears, so second postcondition holds.
  // Therefore out1 must be 4.
  // We'll encode this reasoning with assertions.
  assert out1 >= 4 by {
    if out1 < 4 {
      assert out1 == 0 || out1 == 1 || out1 == 2 || out1 == 3;
      // But each of these appears in a1, contradicting first postcondition
      assert a1[0] == 0;
      assert a1[1] == 1;
      assert a1[2] == 2;
      assert a1[3] == 3;
      // So out1 cannot be any of these
    }
  }
  assert out1 <= 4 by {
    // 4 does not appear in a1
    assert forall k :: 0 <= k < |a1| ==> a1[k] != 4;
    // If out1 > 4, then 4 < out1, so by second postcondition, 4 must appear in a1
    // But it doesn't, so out1 <= 4.
    if out1 > 4 {
      assert 0 <= 4 < out1;
      // By second postcondition, exists k :: 0 <= k < |a1| && a1[k] == 4
      // But we just asserted that no such k exists
    }
  }
  assert out1 == 4;

  var a2: seq<int>:= [0, 1, 2, 2, 4, 9];
  assert a2[..] == [0, 1, 2, 2, 4, 9];
  var out2 := SmallestMissingNumber(a2);
  // Similar reasoning for a2
  assert out2 >= 3 by {
    if out2 < 3 {
      assert out2 == 0 || out2 == 1 || out2 == 2;
      // But each appears in a2
      assert a2[0] == 0;
      assert a2[1] == 1;
      assert a2[2] == 2 || a2[3] == 2;
    }
  }
  assert out2 <= 3 by {
    // 3 does not appear in a2
    assert forall k :: 0 <= k < |a2| ==> a2[k] != 3;
    if out2 > 3 {
      assert 0 <= 3 < out2;
      // By second postcondition, exists k :: 0 <= k < |a2| && a2[k] == 3
      // Contradiction
    }
  }
  assert out2 == 3;

  var a3: seq<int> := [2, 3, 5, 8, 9];
  assert a3[..] == [2, 3, 5, 8, 9];
  var out3 := SmallestMissingNumber(a3);
  // For a3, 0 does not appear, so out3 must be 0.
  assert out3 >= 0 by {
    // trivial
  }
  assert out3 <= 0 by {
    // If out3 > 0, then 0 < out3, so by second postcondition, 0 must appear in a3
    // But it doesn't
    assert forall k :: 0 <= k < |a3| ==> a3[k] != 0;
    if out3 > 0 {
      assert 0 <= 0 < out3;
      // By second postcondition, exists k :: 0 <= k < |a3| && a3[k] == 0
      // Contradiction
    }
  }
  assert out3 == 0;
}


