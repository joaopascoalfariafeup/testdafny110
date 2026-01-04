// Checks if all characters in a string are equal 
// (i.e., it does not hve two distinct characters).
method AllCharactersSame(s: string) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < j < |s| ==> s[i] == s[j]
{
    if |s| > 1 {
        var firstChar := s[0];
        for i := 1 to |s|
            invariant forall j, k :: 0 <= j < k < i ==> s[j] == s[k]
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
    assert s1[0] != s1[1]; // proof helper (counter example)
    var r1 := AllCharactersSame(s1); 
    assert ! r1;

    var r2 := AllCharactersSame("aa"); assert r2; 
    var r3 := AllCharactersSame("a"); assert r3; 
    var r4 := AllCharactersSame(""); assert r4;
}