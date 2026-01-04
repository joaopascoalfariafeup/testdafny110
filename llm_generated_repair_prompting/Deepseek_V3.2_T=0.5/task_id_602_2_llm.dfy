// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists k, l :: 0 <= k < l < |s| && s[k] == s[l] && c == s[k]
  ensures !found ==> forall k, l :: 0 <= k < l < |s| ==> s[k] != s[l]
{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
      invariant !found ==> forall m, n :: 0 <= m < i && m < n < |s| ==> s[m] != s[n]
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
          invariant !found ==> forall n :: i < n < j ==> s[i] != s[n]
        {
            if s[i] == s[j] {
                found := true;
                c := s[i];
                return;
            }
        }
    }
    c := ' ';
}

// Test cases checked statically by Dafny.
method FindFirstRepeatedCharTest(){
    // First character is repeated
    var s1 := "abcabc";
    var found1, out1 := FindFirstRepeatedChar(s1);
    // Helper assertions to trigger verification
    assert |s1| == 6;
    assert s1[0] == 'a' && s1[3] == 'a';
    assert 0 <= 0 < 3 < |s1| && s1[0] == s1[3];
    assert found1 && out1 == 'a';

    // Middle character is repeated
    var s2 := "axbcx";
    var found2, out2 := FindFirstRepeatedChar(s2);
    // Helper assertions
    assert |s2| == 5;
    assert s2[1] == 'x' && s2[4] == 'x';
    assert 0 <= 1 < 4 < |s2| && s2[1] == s2[4];
    assert found2 && out2 == 'x';

    // No repeated characters
    var s4 := "123456";
    var found4, out4 := FindFirstRepeatedChar(s4);
    assert !found4;
}

