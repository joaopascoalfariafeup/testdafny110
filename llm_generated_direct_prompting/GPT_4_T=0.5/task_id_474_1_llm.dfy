// Replace all occurrences of oldChar in string s by newChar 
// and return the resulting string.
method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
  ensures forall k :: 0 <= k < |s| ==> (s[k] == oldChar ==> v[k] == newChar) && (s[k] != oldChar ==> v[k] == s[k])
  ensures |v| == |s|
{
    v := [];
    for i := 0 to |s|
      invariant |v| == i
      invariant forall k :: 0 <= k < i ==> (s[k] == oldChar ==> v[k] == newChar) && (s[k] != oldChar ==> v[k] == s[k])
    {
        if s[i] == oldChar {
            v := v + [newChar];
        }
        else {
            v := v + [s[i]];
        }
    }
}


// Test cases checked statically
method ReplaceCharsTest(){
    // single occurrence
    var out1 := ReplaceChars("polygon", 'y', 'i');
    assert out1 == "poligon";

    // multiple occurrences
    var out2 := ReplaceChars("polygon", 'o', 'a');
    assert out2 == "palygan";

    // no occurrence
    var out3 := ReplaceChars("polygon", 'a', 'b');
    assert out3 == "polygon";
}
