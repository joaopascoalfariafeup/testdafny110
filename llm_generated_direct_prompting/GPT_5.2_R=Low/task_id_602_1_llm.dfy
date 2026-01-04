// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==>
            (exists i, j :: 0 <= i < j < |s| &&
              c == s[i] && s[i] == s[j] &&
              (forall p, q :: 0 <= p < q < |s| && p < i ==> s[p] != s[q]))
  ensures !found ==> c == ' '
  ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
      invariant 0 <= i <= |s|
      invariant !found
      invariant forall p, q :: 0 <= p < q < |s| && p < i ==> s[p] != s[q]
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
          invariant 0 <= i <= |s|
          invariant i + 1 <= j <= |s|
          invariant !found
          invariant forall p, q :: 0 <= p < q < |s| && p < i ==> s[p] != s[q]
          invariant forall k :: i + 1 <= k < j ==> s[i] != s[k]
        {
            if s[i] == s[j] {
                assert 0 <= i < j < |s|;
                assert (forall p, q :: 0 <= p < q < |s| && p < i ==> s[p] != s[q]);
                return true, s[i];
            }
        }
    }
    return false, ' ';
}

// Test cases checked statically by Dafny.
method FindFirstRepeatedCharTest(){
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
