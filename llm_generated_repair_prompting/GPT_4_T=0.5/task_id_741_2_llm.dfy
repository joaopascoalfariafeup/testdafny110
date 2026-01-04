// Checks if all characters in a string are equal 
// (i.e., it does not have two distinct characters).
method AllCharactersSame(s: string) returns (result: bool)
  ensures result == (forall i, j :: 0 <= i < j < |s| ==> s[i] == s[j])
{
    if |s| > 1 {
        var firstChar := s[0];
        for i := 1 to |s|
            invariant 0 <= i <= |s|
            invariant forall k :: 0 <= k < i ==> s[k] == firstChar
        {
            if s[i] != firstChar {
                return false;
            }
        }
    }
    return true;
}

// Test cases checked statically.
method AllCharactersSameTest(){
    var s1 := "axa";
    var r1 := AllCharactersSame(s1); 
    assert ! r1;

    var r2 := AllCharactersSame("aa"); assert r2; 
    var r3 := AllCharactersSame("a"); assert r3; 
    var r4 := AllCharactersSame(""); assert r4;
}
