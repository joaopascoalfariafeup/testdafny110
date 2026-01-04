// Checks if a string contains the letter 'z' or 'Z'
method ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
    result := false;
    for i := 0 to |s| - 1
      invariant 0 <= i <= |s|
      invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
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

