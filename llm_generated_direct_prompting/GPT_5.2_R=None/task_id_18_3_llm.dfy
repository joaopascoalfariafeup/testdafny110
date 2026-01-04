// Remove from the first string all characters which are present in the second string.
// Preserves the order of the remaining elements.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures forall k :: 0 <= k < |v| ==> !(v[k] in s2)
  ensures exists idxs: seq<int> ::
            |idxs| == |v| &&
            (forall j :: 0 <= j < |idxs| ==> 0 <= idxs[j] < |s1| && s1[idxs[j]] == v[j] && !(s1[idxs[j]] in s2)) &&
            (forall j :: 0 <= j < |idxs| - 1 ==> idxs[j] < idxs[j+1]) &&
            (forall i :: 0 <= i < |s1| ==> (!(s1[i] in s2) <==> (exists j :: 0 <= j < |idxs| && idxs[j] == i)))
{
  v := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant forall k :: 0 <= k < |v| ==> !(v[k] in s2)
    invariant exists idxs: seq<int> ::
              |idxs| == |v| &&
              (forall j :: 0 <= j < |idxs| ==> 0 <= idxs[j] < i && s1[idxs[j]] == v[j] && !(s1[idxs[j]] in s2)) &&
              (forall j :: 0 <= j < |idxs| - 1 ==> idxs[j] < idxs[j+1]) &&
              (forall t :: 0 <= t < i ==> (!(s1[t] in s2) <==> (exists j :: 0 <= j < |idxs| && idxs[j] == t)))
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

