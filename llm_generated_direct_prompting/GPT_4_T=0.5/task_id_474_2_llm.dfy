// Replace all occurrences of oldChar in string s by newChar 
// and return the resulting string.
method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
  ensures v.Length == s.Length
  ensures forall i :: 0 <= i < v.Length ==> (if s[i] == oldChar then v[i] == newChar else v[i] == s[i])
{
    v := [];
    for i := 0 to |s|
      invariant v.Length == i
      invariant forall j :: 0 <= j < i ==> (if s[j] == oldChar then v[j] == newChar else v[j] == s[j])
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
