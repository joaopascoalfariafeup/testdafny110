// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures (!found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]))  // If not found, then no character is repeated in the string
  ensures (found ==> (exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && c == s[i]))  // If found, then there exist i and j such that s[i] equals to s[j] and c equals to s[i]
{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
        invariant 0 <= i <= |s|
        invariant !found ==> (forall k, l :: 0 <= k < l < i ==> s[k] != s[l])  // Until i, no character is repeated in the string
        invariant found ==> (exists k, l :: 0 <= k < l < i && s[k] == s[l] && c == s[k])  // If found, then there exist k and l such that s[k] equals to s[l] and c equals to s[k]
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
            invariant i < j <= |s|
            invariant !found ==> (forall k :: i <= k < j ==> s[i] != s[k])  // Until j, s[i] is not repeated
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
