// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
function {:fuel 20} FilterChars(s: seq<char>, rem: seq<char>): seq<char>
{
  if |s| == 0 then []
  else
    var t := FilterChars(s[..|s|-1], rem);
    if s[|s|-1] in rem then t else t + [s[|s|-1]]
}

lemma FilterCharsExtend(s: seq<char>, rem: seq<char>, c: char)
  ensures FilterChars(s + [c], rem) ==
            (if c in rem then FilterChars(s, rem) else FilterChars(s, rem) + [c])
{
  // Unfold FilterChars on (s + [c])
  assert |s + [c]| > 0;
  assert (s + [c])[..|(s + [c])| - 1] == s;
  assert (s + [c])[|(s + [c])| - 1] == c;
}

method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures v == FilterChars(s1, s2)
{
  v := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant v == FilterChars(s1[..i], s2)
  {
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }

    // Help Dafny connect the loop step with FilterChars' definition
    assert s1[..i+1] == s1[..i] + [s1[i]];
    calc {
      FilterChars(s1[..i+1], s2);
      == { assert s1[..i+1] == s1[..i] + [s1[i]]; }
      FilterChars(s1[..i] + [s1[i]], s2);
      == { FilterCharsExtend(s1[..i], s2, s1[i]); }
      if s1[i] in s2 then FilterChars(s1[..i], s2) else FilterChars(s1[..i], s2) + [s1[i]];
    }
  }
  assert s1[..|s1|] == s1;
}

// Concrete evaluation helpers for the static tests
lemma Eval_FilterChars_1()
  ensures FilterChars("a.b,c;", ".,;") == "abc"
{
  // ';' is removed
  assert ';' in ".,;";
  calc {
    FilterChars("a.b,c;", ".,;");
    == { }
    FilterChars("a.b,c", ".,;");
  }

  // 'c' kept
  assert !('c' in ".,;");
  calc {
    FilterChars("a.b,c", ".,;");
    == { }
    FilterChars("a.b,", ".,;") + ['c'];
  }

  // ',' removed
  assert ',' in ".,;";
  calc {
    FilterChars("a.b,", ".,;");
    == { }
    FilterChars("a.b", ".,;");
  }

  // 'b' kept
  assert !('b' in ".,;");
  calc {
    FilterChars("a.b", ".,;");
    == { }
    FilterChars("a.", ".,;") + ['b'];
  }

  // '.' removed
  assert '.' in ".,;";
  calc {
    FilterChars("a.", ".,;");
    == { }
    FilterChars("a", ".,;");
  }

  // 'a' kept
  assert !('a' in ".,;");
  calc {
    FilterChars("a", ".,;");
    == { }
    FilterChars("", ".,;") + ['a'];
    == { }
    [] + ['a'];
  }

  // Put it all together
  calc {
    FilterChars("a.b,c;", ".,;");
    == { }
    FilterChars("a.b,c", ".,;");
    == { }
    FilterChars("a.b,", ".,;") + ['c'];
    == { }
    FilterChars("a.b", ".,;") + ['c'];
    == { }
    (FilterChars("a.", ".,;") + ['b']) + ['c'];
    == { }
    (FilterChars("a", ".,;") + ['b']) + ['c'];
    == { }
    (([] + ['a']) + ['b']) + ['c'];
    == { }
    "abc";
  }
}

lemma Eval_FilterChars_2()
  ensures FilterChars("exomile", "toxic") == "emle"
{
  // e kept
  assert !('e' in "toxic");
  // x removed
  assert 'x' in "toxic";
  // o removed
  assert 'o' in "toxic";
  // m kept
  assert !('m' in "toxic");
  // i removed
  assert 'i' in "toxic";
  // l kept
  assert !('l' in "toxic");
  // e kept
  assert !('e' in "toxic");

  calc {
    FilterChars("exomile", "toxic");
    == { }
    FilterChars("exomil", "toxic") + ['e'];      // last 'e' kept
    == { }
    (FilterChars("exomi", "toxic") + ['l']) + ['e']; // 'l' kept
    == { }
    (FilterChars("exom", "toxic") + ['l']) + ['e'];  // 'i' removed
    == { }
    ((FilterChars("exo", "toxic") + ['m']) + ['l']) + ['e']; // 'm' kept
    == { }
    ((FilterChars("ex", "toxic") + ['m']) + ['l']) + ['e'];  // 'o' removed
    == { }
    ((FilterChars("e", "toxic") + ['m']) + ['l']) + ['e'];   // 'x' removed
    == { }
    (((FilterChars("", "toxic") + ['e']) + ['m']) + ['l']) + ['e']; // first 'e' kept
    == { }
    "emle";
  }
}

// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  assert out1 == FilterChars("a.b,c;", ".,;");
  Eval_FilterChars_1();
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  assert out2 == FilterChars("exomile", "toxic");
  Eval_FilterChars_2();
  assert out2 == "emle";
}
