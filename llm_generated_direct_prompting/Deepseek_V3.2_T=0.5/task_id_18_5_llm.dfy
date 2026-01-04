// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1
  ensures forall i :: 0 <= i < |v| ==> !(v[i] in s2)
  ensures forall i, j :: 0 <= i < j < |v| ==> exists k, l :: 0 <= k < l < |s1| && s1[k] == v[i] && s1[l] == v[j]
  ensures forall k :: 0 <= k < |s1| && !(s1[k] in s2) ==> exists i :: 0 <= i < |v| && v[i] == s1[k]
{
  v := [];
  for i := 0 to |s1|
    invariant |v| <= i
    invariant forall j :: 0 <= j < |v| ==> v[j] in s1
    invariant forall j :: 0 <= j < |v| ==> !(v[j] in s2)
    invariant forall j, m :: 0 <= j < m < |v| ==> exists p, q :: 0 <= p < q < i && s1[p] == v[j] && s1[q] == v[m]
    invariant forall p :: 0 <= p < i && !(s1[p] in s2) ==> exists j :: 0 <= j < |v| && v[j] == s1[p]
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

