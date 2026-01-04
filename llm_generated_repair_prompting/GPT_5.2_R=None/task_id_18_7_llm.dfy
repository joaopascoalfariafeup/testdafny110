// Helper: filter s1 by removing characters that occur in s2, preserving order
ghost function {:fuel 50} RemoveCharsSpec(s1: string, s2: string): string
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

// One-step unfolding lemma, useful for loops
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

// Concrete unfolding helper: builds RemoveCharsSpec(prefix) from RemoveCharsSpec(shorterPrefix)
lemma RemoveCharsSpecExtendByOne(s: string, s2: string)
  requires |s| > 0
  ensures RemoveCharsSpec(s, s2) ==
            (if s[|s|-1] in s2
             then RemoveCharsSpec(s[..|s|-1], s2)
             else RemoveCharsSpec(s[..|s|-1], s2) + [s[|s|-1]])
{
}

// Proof by unfolding along recursion (removes '.', ',', ';')
lemma RemoveCharsSpecConcrete_abc()
  ensures RemoveCharsSpec("a.b,c;", ".,;") == "abc"
{
  calc {
    RemoveCharsSpec("a.b,c;", ".,;");
    == { RemoveCharsSpecExtendByOne("a.b,c;", ".,;") }
    RemoveCharsSpec("a.b,c", ".,;");
    == { RemoveCharsSpecExtendByOne("a.b,c", ".,;") }
    RemoveCharsSpec("a.b,", ".,;") + ['c'];
    == { RemoveCharsSpecExtendByOne("a.b,", ".,;") }
    RemoveCharsSpec("a.b", ".,;") + ['c'];
    == { RemoveCharsSpecExtendByOne("a.b", ".,;") }
    RemoveCharsSpec("a.", ".,;") + ['b'] + ['c'];
    == { RemoveCharsSpecExtendByOne("a.", ".,;") }
    RemoveCharsSpec("a", ".,;") + ['b'] + ['c'];
    == { RemoveCharsSpecExtendByOne("a", ".,;") }
    "" + ['a'] + ['b'] + ['c'];
    == { }
    "abc";
  }
}

// Proof by unfolding along recursion (removes 'x','o','i')
lemma RemoveCharsSpecConcrete_emle()
  ensures RemoveCharsSpec("exomile", "toxic") == "emle"
{
  calc {
    RemoveCharsSpec("exomile", "toxic");
    == { RemoveCharsSpecExtendByOne("exomile", "toxic") }
    RemoveCharsSpec("exomil", "toxic") + ['e'];
    == { RemoveCharsSpecExtendByOne("exomil", "toxic") }
    RemoveCharsSpec("exomi", "toxic") + ['l'] + ['e'];
    == { RemoveCharsSpecExtendByOne("exomi", "toxic") }
    RemoveCharsSpec("exom", "toxic") + ['l'] + ['e'];
    == { RemoveCharsSpecExtendByOne("exom", "toxic") }
    RemoveCharsSpec("exo", "toxic") + ['m'] + ['l'] + ['e'];
    == { RemoveCharsSpecExtendByOne("exo", "toxic") }
    RemoveCharsSpec("ex", "toxic") + ['m'] + ['l'] + ['e'];
    == { RemoveCharsSpecExtendByOne("ex", "toxic") }
    RemoveCharsSpec("e", "toxic") + ['m'] + ['l'] + ['e'];
    == { RemoveCharsSpecExtendByOne("e", "toxic") }
    "" + ['e'] + ['m'] + ['l'] + ['e'];
    == { }
    "emle";
  }
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

