// Auxiliary function to check if a character is repeated in a string
ghost function IsCharRepeated(s: string, i: int, c: char): bool
{
    if i >= |s| then false else (s[i] == c || IsCharRepeated(s, i + 1, c))
}

// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures !found ==> (forall i :: 0 <= i < |s| ==> !IsCharRepeated(s, i + 1, s[i]))
    ensures found ==> IsCharRepeated(s, 0, c)
{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
        invariant 0 <= i <= |s|
        invariant !found ==> (forall k :: 0 <= k < i ==> !IsCharRepeated(s, k + 1, s[k]))
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
            invariant i + 1 <= j <= |s|
            invariant !found ==> (forall k :: i + 1 <= k < j ==> s[i] != s[k])
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
