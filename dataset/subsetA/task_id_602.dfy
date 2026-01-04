// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] == c && (forall k, l :: 0 <= k < i && k < l < |s| ==> s[k] != s[l])
    ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]

{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
        invariant forall l, r :: 0 <= l < i && l < r < |s| ==> s[l] != s[r]
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
            invariant forall r :: i < r < j ==> s[i] != s[r]
        {
            if s[i] == s[j] {
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
    assert s1[0] == s1[3] == 'a'; // proof helper (example)
    assert found1 && out1 == 'a';

    // Middle character is repeated
    var s2 := "axbcx";
    var found2, out2 := FindFirstRepeatedChar(s2);
    assert s2[1] == s2[4] == 'x'; // proof helper (example)
    assert found2 && out2 == 'x';

    // No repeated characters
    var s4 := "123456";
    var found4, out4 := FindFirstRepeatedChar(s4);
    assert !found4;
}