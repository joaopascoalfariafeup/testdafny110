// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
function {:fuel 20} FilterChars(s: seq<char>, rem: seq<char>): seq<char>
{
  if |s| == 0 then []
  else
    var t := FilterChars(s[..|s|-1], rem);
    if s[|s|-1] in rem then t else t + [s[|s|-1]]
}


method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures v == FilterChars(s1, s2)
{
  v := [];
  for i := 0 to |s1|
    invariant v == FilterChars(s1[..i], s2)
  {
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }

    calc {
      FilterChars(s1[..i+1], s2);
      == { assert s1[..i+1] == s1[..i] + [s1[i]]; }
      FilterChars(s1[..i] + [s1[i]], s2);
    }
  }
  assert s1[..|s1|] == s1;
}

lemma Eval_FilterChars_1()
  ensures FilterChars("a.b,c;", ".,;") == "abc"
{
  assert "a.b,c;" == "a.b,c" + [';'];
  assert "a.b,"  == "a.b" + [','];


  calc {
    FilterChars("a.b,c", ".,;");
    == { assert "a.b,c" == "a.b," + ['c']; }
  }


  calc {
    FilterChars("a.b", ".,;");
    == { assert "a.b" == "a." + ['b']; }
  }

  calc {
    FilterChars("a.", ".,;");
    == { }
    FilterChars("a", ".,;");
  }


}

lemma Eval_FilterChars_2()
  ensures FilterChars("exomile", "toxic") == "emle"
{


  calc {
    FilterChars("exomile", "toxic");
    == { assert "exomile" == "exomil" + ['e']; }
    FilterChars("exomil" + ['e'], "toxic");
    == { assert "exomil" == "exomi" + ['l']; }
    FilterChars("exomi" + ['l'], "toxic") + ['e'];
    == { assert "exomi" == "exom" + ['i']; }
    (FilterChars("exom" + ['i'], "toxic") + ['l']) + ['e'];
    == { assert "exom" == "exo" + ['m']; }
    (FilterChars("exo" + ['m'], "toxic") + ['l']) + ['e'];
    == { assert "exo" == "ex" + ['o']; }
    ((FilterChars("ex" + ['o'], "toxic") + ['m']) + ['l']) + ['e'];
  }
}

// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  Eval_FilterChars_1();
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  Eval_FilterChars_2();
  assert out2 == "emle";
}