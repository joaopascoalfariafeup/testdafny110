// Ghost function to compute the minimum list length
ghost function minListLength<T>(s: seq<seq<T>>): int
  requires |s| > 0
  ensures minListLength(s) >= 0
  ensures forall k :: 0 <= k < |s| ==> minListLength(s) <= |s[k]|
  ensures exists k :: 0 <= k < |s| && minListLength(s) == |s[k]|
{
  if |s| == 1 then |s[0]|
  else if |s[|s|-1]| < minListLength(s[..|s|-1]) then |s[|s|-1]|
  else minListLength(s[..|s|-1])
}

// Finds the length of the shortest list in a non-empty list of lists.
method SmallestListLength<T>(s: seq<seq<T>>) returns (v: int)
  requires |s| > 0
  ensures forall k :: 0 <= k < |s| ==> v <= |s[k]|
  ensures exists k :: 0 <= k < |s| && v == |s[k]|
  ensures v == minListLength(s)
{
  v := |s[0]|;
  for i := 1 to |s|
    invariant forall k :: 0 <= k < i ==> v <= |s[k]|
    invariant exists k :: 0 <= k < i && v == |s[k]|
    invariant v == minListLength(s[..i])
  {
    assert s[..i+1] == s[..i] + [s[i]];
    if |s[i]| < v {
      v := |s[i]|;
    }
  }
  assert s[..|s|] == s;
}

method SmallestListLengthTest(){
  var s1:seq<seq<int>> := [[1],[1,2]];
  var res1 := SmallestListLength(s1);
  assert res1 == 1;

  var s2:seq<seq<int>> := [[1,2],[1,2,3],[1,2,3,4]];
  var res2:=SmallestListLength(s2);
  assert res2 == 2;

  var s3:seq<seq<int>> := [[3,3,3],[4,4,4,4]];
  var res3:=SmallestListLength(s3);
  assert res3 == 3 ;
}
