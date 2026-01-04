// Converts a string to uppercase (only 'a' to 'z' characters are converted).
method ToUppercase(s: string) returns (v: string)
  ensures v.Length == s.Length
  ensures forall i :: 0 <= i < v.Length ==> (s[i] == v[i] || CharToUpper(s[i]) == v[i])
{
    v := "";
    for i := 0 to s.Length
      invariant v.Length == i
      invariant forall k :: 0 <= k < i ==> (s[k] == v[k] || CharToUpper(s[k]) == v[k])
    {
        v := v + CharToUpper(s[i]);
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
