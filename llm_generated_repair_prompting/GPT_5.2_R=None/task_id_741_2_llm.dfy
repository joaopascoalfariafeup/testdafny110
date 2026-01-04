// Checks if all characters in a string are equal 
// (i.e., it does not hve two distinct characters).
method AllCharactersSame(s: string) returns (result: bool)
  ensures result <==> (|s| == 0 || forall i :: 0 <= i < |s| ==> s[i] == s[0])
{
    if |s| > 1 {
        var firstChar := s[0];
        for i := 1 to |s|-1
          invariant 1 <= i <= |s|-1
          invariant firstChar == s[0]
          invariant forall j :: 0 <= j <= i ==> s[j] == firstChar
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
    assert !r1;

    var r2 := AllCharactersSame("aa"); assert r2; 
    var r3 := AllCharactersSame("a"); assert r3; 
    var r4 := AllCharactersSame(""); assert r4;
}
