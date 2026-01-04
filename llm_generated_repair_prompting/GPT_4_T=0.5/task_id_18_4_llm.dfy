// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1 && !(v[i] in s2)
  ensures forall i, j :: 0 <= i < j < |s1| && s1[i] in s1[..|v|] && s1[j] in s1[..|v|] ==> i < j
{
  v := "";
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |v| <= i
    invariant forall k :: 0 <= k < |v| ==> v[k] in s1[..i] && !(v[k] in s2)
    invariant forall k, j :: 0 <= k < j < i && s1[k] in s1[..|v|] && s1[j] in s1[..|v|] ==> k < j
  {
    if !(s1[i] in s2) {
      v := v + s1[i]; // Dafny automatically converts char to string before concatenation
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


