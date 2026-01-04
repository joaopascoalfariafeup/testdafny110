// Checks if all characters in a string are equal
// (i.e., it does not have two distinct characters).
predicate AllSame(s: string)
{
  |s| <= 1 || (forall k :: 0 <= k < |s| ==> s[k] == s[0])
}

// Proof helper: a single differing character witnesses that not all are the same.
lemma NotAllSameWitness(s: string, i: int)
  requires |s| > 1
  requires 0 <= i < |s|
  requires s[i] != s[0]
  ensures !AllSame(s)
{
  if AllSame(s) {
    // From AllSame(s) and |s|>1 we get the forall-branch of the definition
    assert (forall k :: 0 <= k < |s| ==> s[k] == s[0]);
    assert s[i] == s[0];
    assert false;
  }
}

method AllCharactersSame(s: string) returns (result: bool)
  ensures result == AllSame(s)
{
  if |s| > 1 {
    var firstChar := s[0];
    for i := 1 to |s|
      invariant 1 <= i <= |s|
      invariant firstChar == s[0]
      invariant forall k :: 1 <= k < i ==> s[k] == firstChar
    {
      if s[i] != firstChar {
        assert 0 <= i < |s|;
        assert s[i] != s[0];
        NotAllSameWitness(s, i);
        assert !AllSame(s);
        return false;
      }
    }

    // At this point, all positions 1..|s|-1 match s[0], so AllSame(s) holds.
    assert forall k | 0 <= k < |s| ensures s[k] == s[0] {
      if k == 0 {
        // trivial
      } else {
        // since k>=1 and loop ended with i==|s|
        assert 1 <= k < |s|;
        assert s[k] == firstChar;
        assert firstChar == s[0];
      }
    }
    assert AllSame(s);
  } else {
    // |s| <= 1
    assert AllSame(s);
  }
  return true;
}

// Test cases checked statically.
method AllCharactersSameTest() {
  var s1 := "axa";
  // Help Dafny establish the expected AllSame fact for this concrete string
  assert |s1| == 3;
  assert 0 <= 1 < |s1|;
  assert s1[1] != s1[0];
  NotAllSameWitness(s1, 1);
  assert !AllSame(s1);

  var r1 := AllCharactersSame(s1);
  assert !r1;

  var r2 := AllCharactersSame("aa"); assert r2;
  var r3 := AllCharactersSame("a"); assert r3;
  var r4 := AllCharactersSame(""); assert r4;
}
