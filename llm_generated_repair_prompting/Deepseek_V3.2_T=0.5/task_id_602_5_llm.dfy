// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists k, l :: 0 <= k < l < |s| && s[k] == s[l] && c == s[k] &&
                     forall m, n :: 0 <= m < k && m < n < |s| ==> s[m] != s[n]
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
    // Helper to prove found1 is true
    assert |s1| == 6;
    assert s1[0] == 'a' && s1[3] == 'a';
    assert 0 <= 0 < 3 < |s1| && s1[0] == s1[3];
    // The postcondition ensures found1 is true because there exists a repeated character
    // We need to help Dafny see that the postcondition implies found1
    // Actually, the method's postcondition says: if found then ... else ...
    // But we need to prove that found must be true for s1.
    // Let's prove by contradiction: if !found1, then by postcondition, no repeated characters.
    // But we have s1[0] == s1[3], contradiction.
    // We'll add an explicit assertion using the postcondition.
    if !found1 {
        // Then by postcondition, forall k, l :: 0 <= k < l < |s1| ==> s1[k] != s1[l]
        // But we have k=0, l=3 with s1[0] == s1[3]
        assert false;
    }
    assert found1;
    assert out1 == 'a';
    
    // Test with no repeated characters
    var s2 := "abcdef";
    var found2, out2 := FindFirstRepeatedChar(s2);
    assert !found2;
    
    // Test with repeated character not at the beginning
    var s3 := "abca";
    var found3, out3 := FindFirstRepeatedChar(s3);
    // Helper
    assert |s3| == 4;
    assert s3[0] == 'a' && s3[3] == 'a';
    if !found3 {
        // Then no repeated characters, but we have s3[0] == s3[3]
        assert false;
    }
    assert found3;
    assert out3 == 'a';
    
    // Test with empty string
    var s4 := "";
    var found4, out4 := FindFirstRepeatedChar(s4);
    assert !found4;
    
    // Test with single character
    var s5 := "x";
    var found5, out5 := FindFirstRepeatedChar(s5);
    assert !found5;
    
    // Test with two identical characters
    var s6 := "aa";
    var found6, out6 := FindFirstRepeatedChar(s6);
    // Helper
    assert |s6| == 2;
    assert s6[0] == 'a' && s6[1] == 'a';
    if !found6 {
        // Then no repeated characters, but we have s6[0] == s6[1]
        assert false;
    }
    assert found6;
    assert out6 == 'a';
}

