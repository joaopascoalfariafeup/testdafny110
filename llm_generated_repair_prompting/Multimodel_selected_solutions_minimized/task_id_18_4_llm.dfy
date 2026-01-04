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
      == { assert s1[..i+1] == s1[..i] + [s1[i]]; } FilterChars(s1[..i] + [s1[i]], s2);
      == { FilterCharsExtend(s1[..i], s2, s1[i]); } if s1[i] in s2 then FilterChars(s1[..i], s2) else FilterChars(s1[..i], s2) + [s1[i]];
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
    == { assert "a.b,c" == "a.b," + ['c']; } FilterChars("a.b," + ['c'], ".,;");
    == { FilterCharsExtend("a.b,", ".,;", 'c'); } (if 'c' in ".,;" then FilterChars("a.b,", ".,;") else FilterChars("a.b,", ".,;") + ['c']);
  }

  calc {
    FilterChars("a.b,", ".,;");
    == { FilterCharsExtend("a.b", ".,;", ','); } (if ',' in ".,;" then FilterChars("a.b", ".,;") else FilterChars("a.b", ".,;") + [',']);
  }




}

lemma Eval_FilterChars_2()
  ensures FilterChars("exomile", "toxic") == "emle"
{


  calc {
    FilterChars("exomile", "toxic");
    == { assert "exomile" == "exomil" + ['e']; } FilterChars("exomil" + ['e'], "toxic");
    == { FilterCharsExtend("exomil", "toxic", 'e'); } (if 'e' in "toxic" then FilterChars("exomil", "toxic") else FilterChars("exomil", "toxic") + ['e']);
    == { assert "exomil" == "exomi" + ['l']; } FilterChars("exomi" + ['l'], "toxic") + ['e'];
    == { assert "exomi" == "exom" + ['i']; } (FilterChars("exom" + ['i'], "toxic") + ['l']) + ['e'];
    == { FilterCharsExtend("exom", "toxic", 'i'); } ((if 'i' in "toxic" then FilterChars("exom", "toxic") else FilterChars("exom", "toxic") + ['i']) + ['l']) + ['e'];
    == { assert "exom" == "exo" + ['m']; } (FilterChars("exo" + ['m'], "toxic") + ['l']) + ['e'];
    == { FilterCharsExtend("exo", "toxic", 'm'); } (((if 'm' in "toxic" then FilterChars("exo", "toxic") else FilterChars("exo", "toxic") + ['m']) + ['l']) + ['e']);
    == { FilterCharsExtend("ex", "toxic", 'o'); } (((if 'o' in "toxic" then FilterChars("ex", "toxic") else FilterChars("ex", "toxic") + ['o']) + ['m']) + ['l']) + ['e'];
    == { assert "ex" == "e" + ['x']; } ((FilterChars("e" + ['x'], "toxic") + ['m']) + ['l']) + ['e'];
    == { FilterCharsExtend("e", "toxic", 'x'); } (((if 'x' in "toxic" then FilterChars("e", "toxic") else FilterChars("e", "toxic") + ['x']) + ['m']) + ['l']) + ['e'];
    == { } ((FilterChars("e", "toxic") + ['m']) + ['l']) + ['e'];   // 'x' removed
    == { assert "e" == "" + ['e']; } ((FilterChars("" + ['e'], "toxic") + ['m']) + ['l']) + ['e'];
    == { FilterCharsExtend("", "toxic", 'e'); } ((((if 'e' in "toxic" then FilterChars("", "toxic") else FilterChars("", "toxic") + ['e']) + ['m']) + ['l']) + ['e']);
    == { } (((FilterChars("", "toxic") + ['e']) + ['m']) + ['l']) + ['e'];
    == { } "emle";
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