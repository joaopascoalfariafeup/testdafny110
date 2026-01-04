// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
predicate HasRepeatAt(s: string, i: int)
{
  exists j :: i < j < |s| && s[i] == s[j]
}

predicate NoRepeatBefore(s: string, i: int)
{
  forall k :: 0 <= k < i ==> !HasRepeatAt(s, k)
}

predicate FirstRepeatedChar(s: string, c: char)
{
  exists i :: 0 <= i < |s| && s[i] == c && HasRepeatAt(s, i) && NoRepeatBefore(s, i)
}

predicate Unique(s: string)
{
  forall k :: 0 <= k < |s| ==> !HasRepeatAt(s, k)
}

method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> FirstRepeatedChar(s, c)
  ensures !found ==> Unique(s)
{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
      invariant 0 <= i <= |s|
      invariant forall k :: 0 <= k < i ==> !HasRepeatAt(s, k)
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
          invariant i + 1 <= j <= |s|
          invariant forall t :: i + 1 <= t < j ==> s[i] != s[t]
        {
            if s[i] == s[j] {
                assert HasRepeatAt(s, i);
                assert NoRepeatBefore(s, i);
                assert FirstRepeatedChar(s, s[i]);
                return true, s[i];
            }
        }
        assert !HasRepeatAt(s, i);
    }
    assert Unique(s);
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
