// Helper: filter s1 by removing characters that occur in s2, preserving order
ghost function {:fuel 20} RemoveCharsSpec(s1: string, s2: string): string
  ensures forall c :: c in RemoveCharsSpec(s1, s2) ==> !(c in s2)
  ensures forall i :: 0 <= i < |s1| && !(s1[i] in s2) ==> s1[i] in RemoveCharsSpec(s1, s2)
  ensures |RemoveCharsSpec(s1, s2)| <= |s1|
  decreases |s1|
{
  if |s1| == 0 then ""
  else
    var t := RemoveCharsSpec(s1[..|s1|-1], s2);
    if s1[|s1|-1] in s2 then t else t + [s1[|s1|-1]]
}

lemma RemoveCharsSpecStep(s1: string, s2: string, i: int)
  requires 0 <= i < |s1|
  ensures RemoveCharsSpec(s1[..i+1], s2) ==
            (if s1[i] in s2
             then RemoveCharsSpec(s1[..i], s2)
             else RemoveCharsSpec(s1[..i], s2) + [s1[i]])
{
  // Make the slices explicit so Dafny can rewrite to the recursive definition
  assert s1[..i+1] == s1[..i] + [s1[i]];
  assert |s1[..i+1]| == i + 1;
  assert (s1[..i+1])[..|(s1[..i+1])|-1] == s1[..i];
  assert (s1[..i+1])[|(s1[..i+1])|-1] == s1[i];
}

lemma RemoveCharsSpecConcrete_abc()
  ensures RemoveCharsSpec("a.b,c;", ".,;") == "abc"
{
  // Unfold along the recursion (removes '.', ',', ';')
  assert RemoveCharsSpec("a", ".,;") == "a";
  assert RemoveCharsSpec("a.", ".,;") == "a";
  assert RemoveCharsSpec("a.b", ".,;") == "ab";
  assert RemoveCharsSpec("a.b,", ".,;") == "ab";
  assert RemoveCharsSpec("a.b,c", ".,;") == "abc";
  assert RemoveCharsSpec("a.b,c;", ".,;") == "abc";
}

lemma RemoveCharsSpecConcrete_emle()
  ensures RemoveCharsSpec("exomile", "toxic") == "emle"
{
  // Unfold along the recursion (removes 'x','o','i')
  assert RemoveCharsSpec("e", "toxic") == "e";
  assert RemoveCharsSpec("ex", "toxic") == "e";
  assert RemoveCharsSpec("exo", "toxic") == "e";
  assert RemoveCharsSpec("exom", "toxic") == "em";
  assert RemoveCharsSpec("exomi", "toxic") == "em";
  assert RemoveCharsSpec("exomil", "toxic") == "eml";
  assert RemoveCharsSpec("exomile", "toxic") == "emle";
}

method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures v == RemoveCharsSpec(s1, s2)
  ensures forall c :: c in v ==> !(c in s2)
  ensures forall i :: 0 <= i < |s1| && !(s1[i] in s2) ==> (s1[i] in v)
  ensures forall c :: c in s2 ==> !(c in v)
  ensures |v| <= |s1|
{
  v := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant v == RemoveCharsSpec(s1[..i], s2)
    invariant forall c :: c in v ==> !(c in s2)
    invariant |v| <= i
  {
    if !(s1[i] in s2) {
      v := v + [s1[i]];
      // help the prover relate the update to the spec's definition
      assert s1[..i+1] == s1[..i] + [s1[i]];
      RemoveCharsSpecStep(s1, s2, i);
      assert v == RemoveCharsSpec(s1[..i+1], s2);
    } else {
      // branch where the character is removed
      assert s1[..i+1] == s1[..i] + [s1[i]];
      RemoveCharsSpecStep(s1, s2, i);
      assert v == RemoveCharsSpec(s1[..i+1], s2);
    }
  }
  // At loop end, i == |s1|
  assert s1[..|s1|] == s1;
}

method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  RemoveCharsSpecConcrete_abc();
  assert RemoveCharsSpec("a.b,c;", ".,;") == "abc";
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  RemoveCharsSpecConcrete_emle();
  assert RemoveCharsSpec("exomile", "toxic") == "emle";
  assert out2 == "emle";
}
