// Converts a string to uppercase (only 'a' to 'z' characters are converted).
method ToUppercase(s: string) returns (v: string)
{
    v := [];
    for i := 0 to |s|
    {
        v := v + [CharToUpper(s[i])];
    }
}

function CharToUpper(c : char) : char {
    if 'a' <= c <= 'z' then c - ('a' - 'A') else c
}


// Test cases checked statically.
method ToUppercaseTest(){
  var out1 := ToUppercase("person");
  assert out1 == "PERSON";

  var out2 := ToUppercase("final");
  assert out2 == "FINAL";

}