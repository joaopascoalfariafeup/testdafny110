// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1 && v[i] !in s2
  ensures forall i :: 0 <= i < |s1| && s1[i] !in s2 ==> s1[i] in v
  ensures v == Filter(s1, s2)
{
  v := [];
  for i := 0 to |s1|
    invariant |v| <= i
    invariant forall j :: 0 <= j < |v| ==> v[j] in s1[..i] && v[j] !in s2
    invariant v == Filter(s1[..i], s2)
  {
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }
    assert s1[..i+1] == s1[..i] + [s1[i]];
  }
  assert s1[..|s1|] == s1;
}

ghost function Filter(s1: string, s2: string): string
{
  if |s1| == 0 then []
  else if s1[|s1|-1] in s2 then Filter(s1[..|s1|-1], s2)
  else Filter(s1[..|s1|-1], s2) + [s1[|s1|-1]]
}

// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  assert "a.b,c;"[..5] == "a.b,c";
  assert "a.b,c"[..4] == "a.b,";
  assert "a.b,"[..3] == "a.b";
  assert "a.b"[..2] == "a.";
  assert "a."[..1] == "a";
  assert "a"[..0] == "";
  assert Filter("", ".,;") == "";
  assert Filter("a", ".,;") == "a";
  assert Filter("a.", ".,;") == "a";
  assert Filter("a.b", ".,;") == "ab";
  assert Filter("a.b,", ".,;") == "ab";
  assert Filter("a.b,c", ".,;") == "abc";
  assert Filter("a.b,c;", ".,;") == "abc";
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  assert "exomile"[..6] == "exomil";
  assert "exomil"[..5] == "exomi";
  assert "exomi"[..4] == "exom";
  assert "exom"[..3] == "exo";
  assert "exo"[..2] == "ex";
  assert "ex"[..1] == "e";
  assert "e"[..0] == "";
  assert Filter("", "toxic") == "";
  assert Filter("e", "toxic") == "e";
  assert Filter("ex", "toxic") == "e";
  assert Filter("exo", "toxic") == "e";
  assert Filter("exom", "toxic") == "em";
  assert Filter("exomi", "toxic") == "em";
  assert Filter("exomil", "toxic") == "eml";
  assert Filter("exomile", "toxic") == "emle";
  assert out2 == "emle";
}

