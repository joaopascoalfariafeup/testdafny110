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

    assert s1[..i+1] == s1[..i] + [s1[i]];
  }
  assert s1[..|s1|] == s1;
}

lemma Eval_FilterChars_1()
  ensures FilterChars("a.b,c;", ".,;") == "abc"
{
  assert "a.b,c;" == "a.b,c" + [';'];
  assert "a.b,c" == "a.b," + ['c'];
  assert "a.b,"  == "a.b" + [','];
  assert "a.b"   == "a." + ['b'];







}

lemma Eval_FilterChars_2()
  ensures FilterChars("exomile", "toxic") == "emle"
{
  assert "exomile" == "exomil" + ['e'];
  assert "exomil"  == "exomi" + ['l'];
  assert "exomi"   == "exom" + ['i'];
  assert "exom"    == "exo" + ['m'];
  assert "exo"     == "ex" + ['o'];


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