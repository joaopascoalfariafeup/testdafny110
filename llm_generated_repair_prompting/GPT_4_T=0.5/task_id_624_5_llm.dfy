// Converts a string to uppercase (only 'a' to 'z' characters are converted).
method ToUppercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |v| ==> (s[i] == v[i] || CharToUpper(s[i]) == v[i])
{
    v := "";
    for i := 0 to |s|
      invariant |v| == i
      invariant forall k :: 0 <= k < i ==> (s[k] == v[k] || CharToUpper(s[k]) == v[k])
    {
        v := v + CharToString(CharToUpper(s[i]));
    }
}

function CharToUpper(c : char) : char {
    if 'a' <= c <= 'z' then c - ('a' - 'A') else c
}

function CharToString(c : char) : string {
  [c]
}

// Test cases checked statically.
method ToUppercaseTest(){
  var out1 := ToUppercase("person");
  assert out1 == "PERSON";
  assert forall i :: 0 <= i < |out1| ==> ("person"[i] == out1[i] || CharToUpper("person"[i]) == out1[i]);

  var out2 := ToUppercase("final");
  assert out2 == "FINAL";
  assert forall i :: 0 <= i < |out2| ==> ("final"[i] == out2[i] || CharToUpper("final"[i]) == out2[i]);
}
