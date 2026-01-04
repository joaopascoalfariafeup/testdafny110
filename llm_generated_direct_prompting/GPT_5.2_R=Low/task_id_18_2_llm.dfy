// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
function RemoveCharsPrefix(s1: string, s2: string, i: int): string
  requires 0 <= i <= |s1|
  decreases i
{
  if i == 0 then []
  else
    var prev := RemoveCharsPrefix(s1, s2, i - 1);
    if s1[i - 1] in s2 then prev else prev + [s1[i - 1]]
}

lemma RemoveCharsPrefixStep(s1: string, s2: string, i: int)
  requires 0 <= i < |s1|
  ensures RemoveCharsPrefix(s1, s2, i + 1) ==
            (if s1[i] in s2 then RemoveCharsPrefix(s1, s2, i)
             else RemoveCharsPrefix(s1, s2, i) + [s1[i]])
{
}

method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures v == RemoveCharsPrefix(s1, s2, |s1|)
{
  v := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant v == RemoveCharsPrefix(s1, s2, i)
  {
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

