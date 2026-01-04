// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1
  ensures forall i :: 0 <= i < |v| ==> !(v[i] in s2)
  ensures forall i, j :: 0 <= i < j < |s1| && !(s1[i] in s2) && !(s1[j] in s2) ==>
    exists k, l :: 0 <= k < l < |v| && v[k] == s1[i] && v[l] == s1[j]
{
  v := [];
  for i := 0 to |s1|
    invariant |v| <= i
    invariant forall k :: 0 <= k < |v| ==> v[k] in s1
    invariant forall k :: 0 <= k < |v| ==> !(v[k] in s2)
    invariant forall m, n :: 0 <= m < n < i && !(s1[m] in s2) && !(s1[n] in s2) ==>
      exists p, q :: 0 <= p < q < |v| && v[p] == s1[m] && v[q] == s1[n]
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

