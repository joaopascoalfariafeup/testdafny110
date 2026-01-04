// Replace all occurrences of oldChar in string s by newChar 
// and return the resulting string.
function ReplaceSeq(s: seq<char>, oldChar: char, newChar: char): seq<char>
{
    if |s| == 0 then []
    else
      ReplaceSeq(s[..|s|-1], oldChar, newChar) +
      [if s[|s|-1] == oldChar then newChar else s[|s|-1]]
}

method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures v == ReplaceSeq(s, oldChar, newChar)
    ensures forall i :: 0 <= i < |s| ==> v[i] == (if s[i] == oldChar then newChar else s[i])
{
    v := [];
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant |v| == i
        invariant v == ReplaceSeq(s[..i], oldChar, newChar)
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
