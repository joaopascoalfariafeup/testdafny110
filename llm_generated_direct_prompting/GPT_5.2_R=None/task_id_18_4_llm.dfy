// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures forall k :: 0 <= k < |v| ==> !(v[k] in s2)
  ensures forall c :: c in v ==> c in s1
  ensures forall i, j :: 0 <= i < j < |v| ==> exists p, q :: 0 <= p < q < |s1| && s1[p] == v[i] && s1[q] == v[j]
  ensures exists idxs: seq<int> ::
            |idxs| == |v| &&
            (forall t :: 0 <= t < |idxs| ==> 0 <= idxs[t] < |s1|) &&
            (forall t :: 0 <= t < |idxs| ==> v[t] == s1[idxs[t]] && !(s1[idxs[t]] in s2)) &&
            (forall t :: 0 <= t < |idxs| - 1 ==> idxs[t] < idxs[t+1])
{
  v := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant forall k :: 0 <= k < |v| ==> !(v[k] in s2)
    invariant forall c :: c in v ==> c in s1[..i]
    invariant exists idxs: seq<int> ::
              |idxs| == |v| &&
              (forall t :: 0 <= t < |idxs| ==> 0 <= idxs[t] < i) &&
              (forall t :: 0 <= t < |idxs| ==> v[t] == s1[idxs[t]] && !(s1[idxs[t]] in s2)) &&
              (forall t :: 0 <= t < |idxs| - 1 ==> idxs[t] < idxs[t+1])
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

