// Replaces all spaces, commas and dots in a string with colons.
method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == ReplaceCharWithColon(s[i])
{
    v := [];
    for i := 0 to |s|
        invariant |v| == i
        invariant forall j :: 0 <= j < i ==> v[j] == ReplaceCharWithColon(s[j])
    {
        v := v + [ReplaceCharWithColon(s[i])];
    }
}

// Transformation to apply to each character.
function ReplaceCharWithColon(c: char) : char {
    if c == ' ' || c == ',' || c == '.' then ':' else c
}


// Test cases checked statically.
method ReplaceWithColonTest(){
    var out1 := ReplaceWithColon("Python language, Programming language.");
    assert out1 == "Python:language::Programming:language:";

    var out2 := ReplaceWithColon("a b c,d e f");
    assert out2 == "a:b:c:d:e:f";

    var out3 := ReplaceWithColon("ram reshma,ram rahim");
    assert out3 == "ram:reshma:ram:rahim";
}

