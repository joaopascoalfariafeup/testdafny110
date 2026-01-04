// Checks if a string contains the letter 'z' or 'Z'
method ContainsZ(s: string) returns (result: bool)
  ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{
    result := false;
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < i ==> s[j] != 'z' && s[j] != 'Z'
    {
        if s[i] == 'z' || s[i] == 'Z' {
            assert 0 <= i < |s|;
            assert exists k :: 0 <= k < |s| && (s[k] == 'z' || s[k] == 'Z');
            return true;
        }
    }
    return false;
}

// Teste cases checked statically
method ContainsZTest() {
  var s1 := "pythonz";
  // Help Dafny establish the existential in the postcondition
  assert 0 <= 6 < |s1|;
  assert s1[6] == 'z';
  assert exists i :: 0 <= i < |s1| && (s1[i] == 'z' || s1[i] == 'Z');

  var out1 := ContainsZ(s1);
  assert out1;

  var s2 := "XYZ.";
  // Help Dafny establish the existential in the postcondition
  assert 0 <= 2 < |s2|;
  assert s2[2] == 'Z';
  assert exists i :: 0 <= i < |s2| && (s2[i] == 'z' || s2[i] == 'Z');

  var out2 := ContainsZ(s2);
  assert out2;

  var out3 := ContainsZ("  lang  .");
  assert !out3;
}
