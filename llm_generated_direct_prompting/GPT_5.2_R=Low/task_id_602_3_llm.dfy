// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==>
            (exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && c == s[i] &&
              (forall k :: 0 <= k < i ==> (forall l :: k < l < |s| ==> s[k] != s[l])))
  ensures !found ==>
            c == ' ' &&
            (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
      invariant 0 <= i <= |s|
      invariant forall k :: 0 <= k < i ==> forall l :: k < l < |s| ==> s[k] != s[l]
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
          invariant i + 1 <= j <= |s|
          invariant forall l :: i + 1 <= l < j ==> s[i] != s[l]
        {
            if s[i] == s[j] {
                assert forall k :: 0 <= k < i ==> forall l :: k < l < |s| ==> s[k] != s[l];
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
