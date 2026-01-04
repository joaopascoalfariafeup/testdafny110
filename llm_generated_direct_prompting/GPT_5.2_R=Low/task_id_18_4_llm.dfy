// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
function {:fuel 20} RemoveCharsSpec(s1: string, s2: string): string
{
  if |s1| == 0 then ""
  else
    var t := RemoveCharsSpec(s1[..|s1|-1], s2);
    if s1[|s1|-1] in s2 then t else t + [s1[|s1|-1]]
}

method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures v == RemoveCharsSpec(s1, s2)
{
  v := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant v == RemoveCharsSpec(s1[..i], s2)
  {
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }
    assert RemoveCharsSpec(s1[..i+1], s2) ==
      (if s1[i] in s2 then RemoveCharsSpec(s1[..i], s2) else RemoveCharsSpec(s1[..i], s2) + [s1[i]]);
  }
}



// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  assert out2 == "emle";
}

