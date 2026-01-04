method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures (!found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])) // If not found, then there are no repeated characters in the string
  ensures (found ==> (forall i, j :: 0 <= i < j < |s| ==> (s[i] == s[j] && c == s[i]) ==> (forall k, l :: 0 <= k < l < j ==> s[k] != s[l]))) // If found, then c is the first repeated character in the string
{
    found := false;
    c := ' ';
    
    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant (!found ==> (forall k, l :: 0 <= k < l < i ==> s[k] != s[l])) // No repeated characters in the substring from position 0 to i-1
        invariant (found ==> (forall k, l :: 0 <= k < l < i ==> (s[k] == s[l] && c == s[k]) ==> (forall m, n :: 0 <= m < n < l ==> s[m] != s[n]))) // If found, then c is the first repeated character in the substring from position 0 to i-1
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s| - 1
            invariant i < j <= |s|
            invariant (!found ==> (forall k :: i < k < j ==> s[i] != s[k])) // No repetition of s[i] in the substring from position i+1 to j-1
            invariant (found ==> (forall k :: i < k < j ==> (s[i] == s[k] && c == s[i]) ==> (forall m :: i < m < k ==> s[i] != s[m]))) // If found, then c is the first repeated character in the substring from position i+1 to j-1
        {
            if s[i] == s[j] {
                found := true;
                c := s[i];
                break;
            }
        }
        if found {
            break;
        }
    }
}

method FindFirstRepeatedCharTest(){
    var s1 := "abcabc";
    var found1, out1 := FindFirstRepeatedChar(s1);
    assert found1 && out1 == 'a';

    var s2 := "axbcx";
    var found2, out2 := FindFirstRepeatedChar(s2);
    assert found2 && out2 == 'x';

    var s4 := "123456";
    var found4, out4 := FindFirstRepeatedChar(s4);
    assert !found4;
}
