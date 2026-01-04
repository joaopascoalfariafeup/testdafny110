// Finds the length of the shortest list in a non-empty list of lists.
method SmallestListLength<T>(s: seq<seq<T>>) returns (v: int)
  requires |s| > 0
  ensures exists k :: 0 <= k < |s| && v == |s[k]|
  ensures forall k :: 0 <= k < |s| ==> v <= |s[k]|
{
  v := |s[0]|;
  for i := 1 to |s|
    invariant 1 <= i <= |s|
    invariant exists k :: 0 <= k < i && v == |s[k]|
    invariant forall k :: 0 <= k < i ==> v <= |s[k]|
  {
    if |s[i]| < v {
      v := |s[i]|;
    }
  }
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

