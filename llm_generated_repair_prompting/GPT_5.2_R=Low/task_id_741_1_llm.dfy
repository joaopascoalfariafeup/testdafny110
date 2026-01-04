// Checks if all characters in a string are equal 
// (i.e., it does not hve two distinct characters).
predicate AllSame(s: string)
{
    |s| <= 1 || (forall k :: 0 <= k < |s| ==> s[k] == s[0])
}

method AllCharactersSame(s: string) returns (result: bool)
    ensures result == AllSame(s)
{
    if |s| > 1 {
        var firstChar := s[0];
        for i := 1 to |s|
            invariant 1 <= i <= |s|
            invariant firstChar == s[0]
            invariant forall k :: 1 <= k < i ==> s[k] == firstChar
        {
            if s[i] != firstChar {
                assert 0 <= i < |s|;
                assert s[i] != s[0];
                assert !AllSame(s);
                return false;
            }
        }
        assert AllSame(s);
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
