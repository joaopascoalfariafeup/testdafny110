// A predicate stating that all characters in s are pairwise distinct
ghost predicate AllDistinct(s: string)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// Finds the first repeated character in a string. Returns a pair (found, c) where
// found is true if a repeated character was found, and c is the repeated character.
//
// "First repeated" means: the returned character is the one whose second occurrence
// has the smallest index among all repeated characters.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==>
            exists i, j ::
              0 <= i < j < |s| &&
              s[i] == s[j] &&
              c == s[i] &&
              // no repeats strictly before i
              (forall p, q :: 0 <= p < q < i ==> s[p] != s[q])
  ensures found ==>
            exists i, j ::
              0 <= i < j < |s| &&
              s[i] == s[j] &&
              c == s[i] &&
              // the second occurrence j is minimal among all repeats
              (forall p, q :: 0 <= p < q < |s| && s[p] == s[q] ==> j <= q)
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

        // show minimality of this j: no repeat can have second index < j
        // (If q < j and s[p]==s[q], then either:
        //   - q < i, contradicting the outer invariant; or
        //   - q == i, contradicting the inner-loop invariant established for this j.)
        assert forall p, q :: 0 <= p < q < |s| && s[p] == s[q] ==> j <= q by {
          forall p, q | 0 <= p < q < |s| && s[p] == s[q]
            ensures j <= q
          {
            if q < j {
              if q < i {
                // outer invariant says all pairs before i are distinct, contradiction
                assert 0 <= p < q < i;
                assert s[p] != s[q];
                assert false;
              } else {
                // since i < j and q < j and not (q < i), we have q == i
                assert q == i;
                // inner invariant gives s[i] != s[k] for all i<k<j; instantiate with k=p
                assert i < p < j;
                assert s[i] != s[p];
                // but s[p]==s[q]==s[i], contradiction
                assert s[p] == s[i];
                assert false;
              }
            }
          }
        }

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
        forall p, q | 0 <= p < q < i + 1
          ensures s[p] != s[q]
        {
          if q < i {
            // covered by previous outer invariant
            assert s[p] != s[q];
          } else {
            // since q < i+1 and not (q < i), we have q == i
            assert q == i;
            assert p < i;

            // Use the outer invariant instantiated with (p,i): since 0<=p<i and q==i<i+1,
            // we get s[p] != s[i].
            assert 0 <= p < i;
            assert s[p] != s[i];
            assert s[p] != s[q];
          }
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
  // helper: show 'a' is the unique earliest repeat by minimal second occurrence
  assert s1[0] == 'a' && s1[3] == 'a';
  assert exists i, j :: 0 <= i < j < |s1| && s1[i] == s1[j] && s1[i] == 'a' && j == 3;
  assert found1 && out1 == 'a';

  // Middle character is repeated
  var s2 := "axbcx";
  var found2, out2 := FindFirstRepeatedChar(s2);
  assert s2[1] == 'x' && s2[4] == 'x';
  assert exists i, j :: 0 <= i < j < |s2| && s2[i] == s2[j] && s2[i] == 'x' && j == 4;
  assert found2 && out2 == 'x';

  // No repeated characters
  var s4 := "123456";
  var found4, out4 := FindFirstRepeatedChar(s4);
  assert !found4;
}
