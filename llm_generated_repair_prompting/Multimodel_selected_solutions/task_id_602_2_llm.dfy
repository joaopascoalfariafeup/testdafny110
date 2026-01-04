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
            invariant forall i', j' :: 0 <= i' < i && i' < j' < |s| ==> s[i'] != s[j']
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
    assert s1[0] == 'a' && s1[3] == 'a';
    assert s1[0] == s1[3];
    var found1, out1 := FindFirstRepeatedChar(s1);
    assert 0 < 3 < |s1| && s1[0] == s1[3] && s1[0] == 'a';
    assert forall i', j' :: 0 <= i' < 0 && i' < j' < |s1| ==> s1[i'] != s1[j'];
    assert found1 && out1 == 'a';

    // Middle character is repeated
    var s2 := "axbcx";
    assert s2[1] == 'x' && s2[4] == 'x';
    assert s2[1] == s2[4];
    assert s2[0] != s2[1] && s2[0] != s2[2] && s2[0] != s2[3] && s2[0] != s2[4];
    var found2, out2 := FindFirstRepeatedChar(s2);
    assert 1 < 4 < |s2| && s2[1] == s2[4] && s2[1] == 'x';
    assert forall j' :: 0 < j' < |s2| ==> s2[0] != s2[j'];
    assert found2 && out2 == 'x';

    // No repeated characters
    var s4 := "123456";
    assert s4[0] != s4[1] && s4[0] != s4[2] && s4[0] != s4[3] && s4[0] != s4[4] && s4[0] != s4[5];
    assert s4[1] != s4[2] && s4[1] != s4[3] && s4[1] != s4[4] && s4[1] != s4[5];
    assert s4[2] != s4[3] && s4[2] != s4[4] && s4[2] != s4[5];
    assert s4[3] != s4[4] && s4[3] != s4[5];
    assert s4[4] != s4[5];
    var found4, out4 := FindFirstRepeatedChar(s4);
    assert !found4;
}

