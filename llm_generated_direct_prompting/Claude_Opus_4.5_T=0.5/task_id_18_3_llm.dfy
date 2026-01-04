// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall k :: 0 <= k < |v| ==> v[k] in s1 && v[k] !in s2
  ensures forall k :: 0 <= k < |s1| ==> (s1[k] !in s2 ==> s1[k] in v)
  ensures v == Filter(s1, s2)
{
  v := [];
  for i := 0 to |s1|
    invariant v == Filter(s1[..i], s2)
  {
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }
  }
}

ghost function Filter(s1: string, s2: string): string
{
  if |s1| == 0 then []
  else if s1[|s1|-1] in s2 then Filter(s1[..|s1|-1], s2)
  else Filter(s1[..|s1|-1], s2) + [s1[|s1|-1]]
}

// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  assert out2 == "emle";
}

