// Checks if a string contains the letter 'z' or 'Z'
method ContainsZ(s: string) returns (result: bool)
  ensures result <==> (exists k :: 0 <= k < |s| && (s[k] == 'z' || s[k] == 'Z'))
{
    result := false;
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant result == false
      invariant forall k :: 0 <= k < i ==> s[k] != 'z' && s[k] != 'Z'
    {
        if s[i] == 'z' || s[i] == 'Z' {
            assert 0 <= i < |s|;
            assert exists k :: 0 <= k < |s| && (s[k] == 'z' || s[k] == 'Z');
            return true;
        }
    }
    assert forall k :: 0 <= k < |s| ==> s[k] != 'z' && s[k] != 'Z';
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
