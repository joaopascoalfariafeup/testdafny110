// Convert a string to lowercase
method ToLowercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall k :: 0 <= k < |s| ==> v[k] == CharToLower(s[k])
{
    v := "";
    for i := 0 to |s|
      invariant |v| == i
      invariant forall k :: 0 <= k < i ==> v[k] == CharToLower(s[k])
    {
        v := v + CharToString(CharToLower(s[i]));
    }
}

// Convert a single character to lowercase
function CharToLower(c : char) : char {
    if 'A' <= c <= 'Z' then c + ('a' - 'A') else c
}

// Convert a character to string
function CharToString(c : char) : string {
    SeqToString([c])
}

// Function to convert a sequence of characters to a string
function {:fuel 5} SeqToString(s: seq<char>): string
  ensures |s| == |result|
  ensures forall k :: 0 <= k < |s| ==> s[k] == result[k]
{
  if |s| == 0 then ""
  else CharToString(s[0]) + SeqToString(s[1..])
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

