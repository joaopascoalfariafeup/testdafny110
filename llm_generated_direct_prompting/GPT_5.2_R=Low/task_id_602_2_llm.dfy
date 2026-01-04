// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
predicate AllDistinct(s: string)
{
  forall i: int, j: int :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate FirstRepeat(s: string, c: char)
{
  exists i: int, j: int ::
    0 <= i < j < |s| &&
    s[i] == c && s[j] == c &&
    (forall k: int :: 0 <= k < i ==> forall l: int :: k < l < |s| ==> s[k] != s[l])
}

method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> FirstRepeat(s, c)
  ensures !found ==> AllDistinct(s)
{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
      invariant 0 <= i <= |s|
      invariant forall k: int :: 0 <= k < i ==> forall l: int :: k < l < |s| ==> s[k] != s[l]
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
          invariant i + 1 <= j <= |s|
          invariant forall t: int :: i + 1 <= t < j ==> s[i] != s[t]
        {
            if s[i] == s[j] {
                assert 0 <= i < j < |s|;
                assert forall k: int :: 0 <= k < i ==> forall l: int :: k < l < |s| ==> s[k] != s[l];
                assert FirstRepeat(s, s[i]);
                return true, s[i];
            }
        }
        assert forall l: int :: i < l < |s| ==> s[i] != s[l];
    }
    assert forall i: int, j: int :: 0 <= i < j < |s| ==> s[i] != s[j];
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
