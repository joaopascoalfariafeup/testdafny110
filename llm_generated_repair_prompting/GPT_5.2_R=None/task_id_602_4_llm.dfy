// A predicate stating that all characters in s are pairwise distinct
ghost predicate AllDistinct(s: string)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// Finds the first repeated character in a string. Returns a pair (found, c) where
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==>
            exists i, j ::
              0 <= i < j < |s| &&
              s[i] == s[j] &&
              c == s[i] &&
              (forall p, q :: 0 <= p < q < i ==> s[p] != s[q])
  ensures !found ==> AllDistinct(s)
{
  found := false;

  // scan the string from left to right (until a repeated character is found)
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    // all pairs strictly before i are distinct
    invariant forall p, q :: 0 <= p < q < i ==> s[p] != s[q]
  {
    // check if the character is repeated in the subsequent positions
    for j := i + 1 to |s|
      invariant i + 1 <= j <= |s|
      invariant i < |s| ==> forall k :: i < k < j ==> s[i] != s[k]
    {
      if s[i] == s[j] {
        // establish "no repeats before i" from the outer loop invariant
        assert forall p, q :: 0 <= p < q < i ==> s[p] != s[q];
        return true, s[i];
      }
    }

    // help the outer invariant for the next i:
    // we have shown s[i] differs from every later position (if i is in range)
    if i < |s| {
      assert forall k :: i < k < |s| ==> s[i] != s[k];

      // Now prove the next-iteration outer invariant:
      // forall p,q :: 0 <= p < q < i+1 ==> s[p] != s[q]
      assert forall p, q :: 0 <= p < q < i + 1 ==> s[p] != s[q] by {
        if q < i {
          // covered by previous outer invariant
          assert s[p] != s[q];
        } else {
          // since q < i+1 and not (q < i), we have q == i
          assert q == i;
          assert p < i;
          // use that s[i] differs from every later position; instantiate with k := i
          assert s[p] != s[i] by {
            assert i < |s|;
            assert s[p] != s[i]; // from the assertion above with k:=i and p<i
          }
          assert s[p] != s[q];
        }
      }
    }
  }

  // if we get here, no character was repeated
  assert AllDistinct(s);
  return false, ' ';
}

// Test cases checked statically by Dafny.
method FindFirstRepeatedCharTest() {
  // First character is repeated
  var s1 := "abcabc";
  var found1, out1 := FindFirstRepeatedChar(s1);
  assert found1 && out1 == 'a';

  // Middle character is repeated
  var s2 := "axbcx";
  var found2, out2 := FindFirstRepeatedChar(s2);
  assert found2 && out2 == 'x';

  // No repeated characters
  var s4 := "123456";
  var found4, out4 := FindFirstRepeatedChar(s4);
  assert !found4;
}
