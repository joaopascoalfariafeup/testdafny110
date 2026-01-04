// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1
  ensures forall i :: 0 <= i < |v| ==> !(v[i] in s2)
  ensures forall i, j :: 0 <= i < j < |v| ==> exists k, l :: 0 <= k < l < |s1| && s1[k] == v[i] && s1[l] == v[j]
{
  v := "";
  var idx := 0;
  while idx < |s1|
    invariant 0 <= idx <= |s1|
    invariant |v| <= idx
    invariant forall k :: 0 <= k < |v| ==> v[k] in s1[..idx]
    invariant forall k :: 0 <= k < |v| ==> !(v[k] in s2)
    invariant forall k, l :: 0 <= k < l < |v| ==> exists m, n :: 0 <= m < n < idx && s1[m] == v[k] && s1[n] == v[l]
  {
    if !(s1[idx] in s2) {
      v := v + [s1[idx]];
    }
    idx := idx + 1;
  }
}

// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  // Helper assertions to prove the test outcome
  assert out1[0] == 'a';
  assert out1[1] == 'b';
  assert out1[2] == 'c';
  assert |out1| == 3;
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  // Helper assertions to prove the test outcome
  assert out2[0] == 'e';
  assert out2[1] == 'm';
  assert out2[2] == 'l';
  assert out2[3] == 'e';
  assert |out2| == 4;
  assert out2 == "emle";
}
