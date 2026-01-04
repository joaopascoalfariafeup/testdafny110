// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1 && v[i] !in s2
  ensures forall i :: 0 <= i < |s1| ==> (s1[i] !in s2 ==> s1[i] in v)
  ensures v == Filter(s1, s2)
{
  v := [];
  for i := 0 to |s1|
    invariant |v| <= i
    invariant forall j :: 0 <= j < |v| ==> v[j] in s1[..i] && v[j] !in s2
    invariant forall j :: 0 <= j < i ==> (s1[j] !in s2 ==> s1[j] in v)
    invariant v == Filter(s1[..i], s2)
  {
    assert s1[..i+1] == s1[..i] + [s1[i]];
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }
  }
  assert s1[..|s1|] == s1;
}

ghost function {:fuel 10} Filter(s1: string, s2: string): string
{
  if |s1| == 0 then []
  else if s1[0] in s2 then Filter(s1[1..], s2)
  else [s1[0]] + Filter(s1[1..], s2)
}

lemma FilterConcat(s1: string, c: char, s2: string)
  ensures Filter(s1 + [c], s2) == if c in s2 then Filter(s1, s2) else Filter(s1, s2) + [c]
{
  if |s1| == 0 {
    assert s1 + [c] == [c];
  } else {
    assert (s1 + [c])[0] == s1[0];
    assert (s1 + [c])[1..] == s1[1..] + [c];
    FilterConcat(s1[1..], c, s2);
  }
}

// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  assert Filter("a.b,c;", ".,;") == "abc";
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  assert Filter("exomile", "toxic") == "emle";
  assert out2 == "emle";
}
