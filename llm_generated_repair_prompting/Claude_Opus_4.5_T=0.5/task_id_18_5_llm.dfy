// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall k :: 0 <= k < |v| ==> v[k] in s1 && v[k] !in s2
  ensures forall k :: 0 <= k < |s1| ==> (s1[k] !in s2 ==> s1[k] in v)
  ensures v == Filter(s1, s2)
{
  v := [];
  for i := 0 to |s1|
    invariant |v| <= i
    invariant forall k :: 0 <= k < |v| ==> v[k] in s1[..i] && v[k] !in s2
    invariant forall k :: 0 <= k < i ==> (s1[k] !in s2 ==> s1[k] in v)
    invariant v == FilterPrefix(s1, s2, i)
  {
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }
  }
  assert s1[..|s1|] == s1;
  FilterEquivalence(s1, s2);
}

ghost function FilterPrefix(s1: string, s2: string, n: int): string
  requires 0 <= n <= |s1|
{
  if n == 0 then []
  else if s1[n-1] in s2 then FilterPrefix(s1, s2, n-1)
  else FilterPrefix(s1, s2, n-1) + [s1[n-1]]
}

ghost function {:fuel 20} Filter(s1: string, s2: string): string
{
  if |s1| == 0 then []
  else if s1[|s1|-1] in s2 then Filter(s1[..|s1|-1], s2)
  else Filter(s1[..|s1|-1], s2) + [s1[|s1|-1]]
}

lemma FilterEquivalence(s1: string, s2: string)
  ensures Filter(s1, s2) == FilterPrefix(s1, s2, |s1|)
{
  FilterEquivalenceHelper(s1, s2, |s1|);
  assert s1[..|s1|] == s1;
}

lemma FilterEquivalenceHelper(s1: string, s2: string, n: int)
  requires 0 <= n <= |s1|
  ensures Filter(s1[..n], s2) == FilterPrefix(s1, s2, n)
{
  if n == 0 {
    assert s1[..0] == [];
  } else {
    FilterEquivalenceHelper(s1, s2, n-1);
    assert s1[..n][..n-1] == s1[..n-1];
  }
}

lemma FilterLemma(s1: string, s2: string)
  ensures Filter(s1, s2) == FilterPrefix(s1, s2, |s1|)
{
  FilterEquivalence(s1, s2);
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
  assert "a.b,"[..(|"a.b,"|-1)] == "a.b";
  assert Filter("a.b,", ".,;") == "ab";
  assert "a.b,c"[..(|"a.b,c"|-1)] == "a.b,";
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
  assert "exom"[..(|"exom"|-1)] == "exo";
  assert Filter("exom", "toxic") == "em";
  assert "exomi"[..(|"exomi"|-1)] == "exom";
  assert Filter("exomi", "toxic") == "em";
  assert "exomil"[..(|"exomil"|-1)] == "exomi";
  assert Filter("exomil", "toxic") == "eml";
  assert Filter("exomile", "toxic") == "emle";
  assert out2 == "emle";
}

