// Checks if a string contains the letter 'z' or 'Z'
method ContainsZ(s: string) returns (result: bool)
    ensures result <==> 'z' in s || 'Z' in s
{
    result := false;
    for i := 0 to |s|
        invariant 'z' !in s[..i] && 'Z' !in s[..i]
    {
        if s[i] == 'z' || s[i] == 'Z' {
            return true;
        }
    }
    return false;

}

// Teste cases checked statically
method ContainsZTest() {
  var s1 := "pythonz";
  var out1 := ContainsZ(s1);
  assert out1;

  var s2 := "XYZ.";
  var out2 := ContainsZ(s2);
  assert out2;

  var out3 := ContainsZ("  lang  .");
  assert !out3;
}