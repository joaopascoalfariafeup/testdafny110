// Finds the first repeated character in a string. Returns a pair (found, c) where
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && c == s[i] &&
                    (forall p, q :: 0 <= p < q < i ==> s[p] != s[q])
  ensures found ==> forall k :: 0 <= k < (var i :| exists j :: i < j < |s| && s[i] == s[j]; i) ==>
                    (forall j :: k < j < |s| ==> s[k] != s[j])
  ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
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
        return true, s[i];
      }
    }

    // help the outer invariant for the next i:
    // we have shown s[i] differs from every later position (if i is in range)
    if i < |s| {
      assert forall k :: i < k < |s| ==> s[i] != s[k];
    }
  }
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
