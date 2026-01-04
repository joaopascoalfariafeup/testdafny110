// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall j :: 0 <= j < |v| ==> !(v[j] in s2)
  ensures forall j :: 0 <= j < |v| ==> v[j] in s1 && (forall k :: 0 <= k < j ==> v[k] != v[j] || v[k] == v[j] && v[j] not in s2)
{
  v := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |v| <= i
    invariant forall j :: 0 <= j < |v| ==> !(v[j] in s2)
    invariant forall j :: 0 <= j < |v| ==> v[j] in s1[..i] && (forall k :: 0 <= k < j ==> v[k] != v[j] || v[k] == v[j] && v[j] not in s2)
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
