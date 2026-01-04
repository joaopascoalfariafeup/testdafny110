// Converts a string to uppercase (only 'a' to 'z' characters are converted).
method ToUppercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == CharToUpper(s[i])
{
    v := [];
    for i := 0 to |s|
      invariant |v| == i
      invariant forall j :: 0 <= j < i ==> v[j] == CharToUpper(s[j])
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
