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
    assert found1;
    // Helper assertions to trigger verification
    assert |s1| == 6;
    assert s1[0] == 'a' && s1[3] == 'a';
    assert 0 <= 0 < 3 < |s1| && s1[0] == s1[3];
    // Prove that out1 must be 'a' using the strengthened postcondition
    // The postcondition says: exists k, l :: 0 <= k < l < |s| && s[k] == s[l] && out1 == s[k] &&
    //                         forall m, n :: 0 <= m < k && m < n < |s| ==> s[m] != s[n]
    // For k=0, the forall condition is vacuously true (since there is no m with 0 <= m < 0).
    // Therefore, k=0 satisfies the condition, and out1 == s[0] == 'a'.
    // We need to help Dafny see that k cannot be greater than 0 because 'a' is repeated at position 0.
    // Actually, the postcondition guarantees that k is the smallest index with a repeated character.
    // Since 'a' at position 0 is repeated, k must be 0.
    // Let's assert a lemma: if there exists a repeated character at position 0, then k must be 0.
    // But we can simply assert out1 == 'a' and let Dafny use the postcondition.
    // We'll add an assertion that uses the postcondition explicitly.
    assert out1 == 'a';
    
    // Test with no repeated characters
    var s2 := "abcdef";
    var found2, out2 := FindFirstRepeatedChar(s2);
    assert !found2;
    
    // Test with repeated character not at the beginning
    var s3 := "abca";
    var found3, out3 := FindFirstRepeatedChar(s3);
    assert found3;
    // The first repeated character is 'a' at position 0 (repeated at position 3)
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
    assert found6;
    assert out6 == 'a';
}
