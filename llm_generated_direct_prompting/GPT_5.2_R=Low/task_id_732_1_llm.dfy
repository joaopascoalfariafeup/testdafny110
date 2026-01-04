// Replaces all spaces, commas and dots in a string with colons.
method ReplaceWithColon(s: string) returns (v: string)
    ensures v == ReplaceWithColonString(s)
{
    v := [];
    for i := 0 to |s|
        invariant v == ReplaceWithColonString(s[..i])
    {
        v := v + [ReplaceCharWithColon(s[i])];
    }
}

// Transformation to apply to each character.
function ReplaceCharWithColon(c: char) : char {
    if c == ' ' || c == ',' || c == '.' then ':' else c
}

function {:fuel 3} ReplaceWithColonString(t: string): string {
    if |t| == 0 then []
    else ReplaceWithColonString(t[..|t|-1]) + [ReplaceCharWithColon(t[|t|-1])]
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

