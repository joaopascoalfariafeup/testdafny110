// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall c :: c in v ==> c in s1 && c !in s2
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1 && v[i] !in s2
  ensures v == Filter(s1, s2)
{
  v := [];
  for i := 0 to |s1|
    invariant v == Filter(s1[..i], s2)
  {
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }
  }
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
  assert "a.b,c;"[..0] == "";
  assert "a.b,c;"[..1] == "a";
  assert "a.b,c;"[..2] == "a.";
  assert "a.b,c;"[..3] == "a.b";
  assert "a.b,c;"[..4] == "a.b,";
  assert "a.b,c;"[..5] == "a.b,c";
  assert Filter("", ".,;") == "";
  assert Filter("a", ".,;") == "a";
  assert Filter("a.", ".,;") == "a";
  assert Filter("a.b", ".,;") == "ab";
  assert Filter("a.b,", ".,;") == "ab";
  assert Filter("a.b,c", ".,;") == "abc";
  assert Filter("a.b,c;", ".,;") == "abc";
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  assert "exomile"[..0] == "";
  assert "exomile"[..1] == "e";
  assert "exomile"[..2] == "ex";
  assert "exomile"[..3] == "exo";
  assert "exomile"[..4] == "exom";
  assert "exomile"[..5] == "exomi";
  assert "exomile"[..6] == "exomil";
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

