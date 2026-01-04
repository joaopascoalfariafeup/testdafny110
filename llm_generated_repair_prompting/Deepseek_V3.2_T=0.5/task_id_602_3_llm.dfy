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
    // Additional helper to prove the postcondition implies out1 == 'a'
    // The postcondition says: found ==> exists k, l :: 0 <= k < l < |s| && s[k] == s[l] && out1 == s[k]
    // We know s[0] == s[3] and 0 < 3, so there exists such k,l. But we need to show that out1 must be 'a'.
    // The method returns the first repeated character found, which is 'a' at position 0.
    // We need to help Dafny see that the method's algorithm guarantees this.
    // Let's add an assertion about the behavior of the algorithm:
    // The outer loop invariant ensures that when i=0, we check s[0] against all subsequent characters.
    // Since s[0] == s[3], the inner loop will find it when j=3 and return with out1 = s[0] = 'a'.
    // We can assert a lemma-like fact: if there exists a repeated character at the earliest position,
    // then the method will return that character.
    // But simpler: we can assert that out1 == 'a' by using the postcondition and the fact that 'a' is the only
    // character that appears at position 0 and is repeated.
    // Actually, the postcondition doesn't guarantee uniqueness of c, but the algorithm does.
    // We'll add a helper assertion that uses the postcondition to derive out1 == 'a'.
    // Since we know s[0] == 'a' and it's repeated, the postcondition says out1 == s[k] for some k where s[k] is repeated.
    // But s[k] could be 'a', 'b', or 'c'? Actually, 'b' and 'c' are also repeated in s1.
    // However, the algorithm finds the *first* repeated character, which is 'a'.
    // The postcondition doesn't specify that it's the first, so we need to strengthen the postcondition.
    // Let's add a postcondition that ensures ordering:
    ensures found ==> exists k, l :: 0 <= k < l < |s| && s[k] == s[l] && c == s[k] &&
                     forall m, n :: 0 <= m < k && m < n < |s| ==> s[m] != s[n]
    // This says that k is the smallest index such that s[k] is repeated.
    // Then in the test, we can prove out1 == 'a' because k must be 0.
    // But we cannot change the method's postcondition? The problem says we can fix preconditions, postconditions, etc.
    // So we should update the method's postcondition to include this ordering property.
}

