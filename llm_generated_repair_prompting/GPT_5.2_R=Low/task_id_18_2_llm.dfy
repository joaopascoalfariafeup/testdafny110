// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
function {:fuel 10} FilterChars(s: seq<char>, rem: seq<char>): seq<char>
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



// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  assert out2 == "emle";
}
