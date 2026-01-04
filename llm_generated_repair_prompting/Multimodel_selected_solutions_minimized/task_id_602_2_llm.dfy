// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> (exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && c == s[i] &&
                      (forall i', j' :: 0 <= i' < i && i' < j' < |s| ==> s[i'] != s[j']))
    ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
        invariant forall i', j' :: 0 <= i' < i && i' < j' < |s| ==> s[i'] != s[j']
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
            invariant forall j' :: i + 1 <= j' < j ==> s[i] != s[j']
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
    assert 0 < 3 < |s1| && s1[0] == s1[3] && s1[0] == 'a';
    assert found1 && out1 == 'a';

    // Middle character is repeated
    var s2 := "axbcx";
    var found2, out2 := FindFirstRepeatedChar(s2);
    assert 1 < 4 < |s2| && s2[1] == s2[4] && s2[1] == 'x';
    assert found2 && out2 == 'x';

    // No repeated characters
    var s4 := "123456";
    var found4, out4 := FindFirstRepeatedChar(s4);
    assert !found4;
}