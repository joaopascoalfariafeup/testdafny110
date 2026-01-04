// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
function RemoveCharsPrefix(s1: string, n: int, s2: string): string
  requires 0 <= n <= |s1|
{
  if n == 0 then ""
  else
    var prev := RemoveCharsPrefix(s1, n - 1, s2);
    if s1[n - 1] in s2 then prev else prev + [s1[n - 1]]
}

method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures v == RemoveCharsPrefix(s1, |s1|, s2)
{
  v := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant v == RemoveCharsPrefix(s1, i, s2)
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

