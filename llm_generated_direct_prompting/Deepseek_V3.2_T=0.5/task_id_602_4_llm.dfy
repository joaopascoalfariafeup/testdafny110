// Finds the first repeated character in a string. Returns a pair (found, c) where 
// found is true if a repeated character was found, and c is the repeated character.
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists k, l :: 0 <= k < l < |s| && s[k] == s[l] && c == s[k] && (forall m, n :: 0 <= m < n < k ==> s[m] != s[n])
  ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
    found := false;
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| 
      invariant !found ==> (forall a, b :: 0 <= a < b < i ==> s[a] != s[b])
      invariant found ==> exists k, l :: 0 <= k < l < |s| && s[k] == s[l] && c == s[k] && (forall m, n :: 0 <= m < n < k ==> s[m] != s[n])
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
          invariant !found ==> (forall b :: i+1 <= b < j ==> s[i] != s[b])
          invariant found ==> exists k, l :: 0 <= k < l < |s| && s[k] == s[l] && c == s[k] && (forall m, n :: 0 <= m < n < k ==> s[m] != s[n])
        {
            if s[i] == s[j] {
                found, c := true, s[i];
                return;
            }
        }
    }
    return;
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
