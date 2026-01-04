// Checks if all characters in a string are equal 
// (i.e., it does not have two distinct characters).
method AllCharactersSame(s: string) returns (result: bool)
  ensures result == (forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j])
{
    if |s| > 1 {
        var firstChar := s[0];
        for i := 1 to |s|
          invariant 1 <= i <= |s|
          invariant forall k :: 0 <= k < i ==> s[k] == firstChar
        {
            if s[i] != firstChar {
                // When we return false, we know there are two different characters
                // s[0] and s[i] are different
                return false;
            }
        }
        // If we get here, all characters equal firstChar
        return true;
    }
    return true;
}

// Test cases checked statically.
method AllCharactersSameTest(){
    var s1 := "axa";
    var r1 := AllCharactersSame(s1); 
    // Add helper assertions to help Dafny verify this
    assert |s1| == 3;
    assert s1[0] == 'a';
    assert s1[1] == 'x';
    assert s1[2] == 'a';
    assert s1[0] != s1[1];  // This shows they're different
    assert ! r1;

    var r2 := AllCharactersSame("aa"); assert r2; 
    var r3 := AllCharactersSame("a"); assert r3; 
    var r4 := AllCharactersSame(""); assert r4;
}
