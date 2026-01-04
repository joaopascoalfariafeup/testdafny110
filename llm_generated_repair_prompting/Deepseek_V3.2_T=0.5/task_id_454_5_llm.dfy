// Checks if a string contains the letter 'z' or 'Z'
method ContainsZ(s: string) returns (result: bool)
  ensures result == exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
    result := false;
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant result == false ==> forall j :: 0 <= j < i ==> s[j] != 'z' && s[j] != 'Z'
      invariant result == true ==> exists j :: 0 <= j < i && (s[j] == 'z' || s[j] == 'Z')
    {
        if s[i] == 'z' || s[i] == 'Z' {
            result := true;
            return;
        }
    }
    return;
}

// Teste cases checked statically
method ContainsZTest() {
  var s1 := "pythonz";
  var out1 := ContainsZ(s1);
  // Helper assertion to verify the postcondition
  assert |s1| == 7;
  assert s1[6] == 'z';
  assert exists i :: 0 <= i < |s1| && (s1[i] == 'z' || s1[i] == 'Z');
  assert out1;

  var s2 := "XYZ.";
  var out2 := ContainsZ(s2);
  // Helper assertion to verify the postcondition
  assert |s2| == 4;
  // Fix: s2[1] is 'Y', not 'Z'. The string "XYZ." has characters: X(0), Y(1), Z(2), .(3)
  // So we should assert s2[2] == 'Z' instead
  assert s2[2] == 'Z';
  assert exists i :: 0 <= i < |s2| && (s2[i] == 'z' || s2[i] == 'Z');
  assert out2;

  var out3 := ContainsZ("  lang  .");
  assert !out3;
}




