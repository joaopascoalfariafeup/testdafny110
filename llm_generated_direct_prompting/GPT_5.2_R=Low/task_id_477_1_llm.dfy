// Convert a string to lowercase
function {:fuel 50} LowerString(s: string): string
{
    if |s| == 0 then ""
    else LowerString(s[..|s|-1]) + [CharToLower(s[|s|-1])]
}

method ToLowercase(s: string) returns (v: string)
    ensures v == LowerString(s)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == CharToLower(s[i])
{
    v := [];
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant v == LowerString(s[..i])
        invariant |v| == i
        invariant forall j :: 0 <= j < i ==> v[j] == CharToLower(s[j])
    {
        v := v + [CharToLower(s[i])];
    }
}

// Convert a single character to lowercase
function CharToLower(c : char) : char {
    if 'A' <= c <= 'Z' then c + ('a' - 'A') else c
}



// Test cases checked statically
method TestToLowercase()
{
    // Test case 1
    var result := ToLowercase("Hello, World!");
    assert result == "hello, world!";

    // Test case 2
    result := ToLowercase("Dafny IS Fun!");
    assert result == "dafny is fun!";

    // Test case 3 - Testing an empty string
    result := ToLowercase("");
    assert result == "";

    // Test case 4 - Testing a string with no alphabetical characters
    result := ToLowercase("1234567890");
    assert result == "1234567890";
}
