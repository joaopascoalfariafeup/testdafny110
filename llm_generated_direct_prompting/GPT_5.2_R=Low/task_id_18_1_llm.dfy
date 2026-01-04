function FilterPrefix(s1: string, s2: string, n: nat): string
  requires n <= |s1|
{
  if n == 0 then []
  else
    var prev := FilterPrefix(s1, s2, n - 1);
    if s1[n - 1] in s2 then prev else prev + [s1[n - 1]]
}

lemma FilterPrefixStep(s1: string, s2: string, i: nat)
  requires i < |s1|
  ensures FilterPrefix(s1, s2, i + 1) ==
            (if s1[i] in s2 then FilterPrefix(s1, s2, i) else FilterPrefix(s1, s2, i) + [s1[i]])
{
}

// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures v == FilterPrefix(s1, s2, |s1|)
{
  v := [];
  for i := 0 to |s1|
    invariant v == FilterPrefix(s1, s2, i)
  {
    FilterPrefixStep(s1, s2, i);
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }
  }
}



// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  assert out2 == "emle";
}

