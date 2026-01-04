// Finds the length of the shortest list in a non-empty list of lists.
method SmallestListLength<T>(s: seq<seq<T>>) returns (v: int)
  requires |s| > 0
  ensures 0 <= v
  ensures forall k :: 0 <= k < |s| ==> v <= |s[k]|
  ensures exists k :: 0 <= k < |s| && v == |s[k]|
{
  v := |s[0]|;
  for i := 1 to |s|
    invariant 1 <= i <= |s|
    invariant 0 <= v
    invariant forall k :: 0 <= k < i ==> v <= |s[k]|
    invariant exists k :: 0 <= k < i && v == |s[k]|
  {
    if |s[i]| < v {
      v := |s[i]|;
      // re-establish the existential invariant after updating v
      assert 0 <= i < i + 1;
      assert v == |s[i]|;
      assert exists k :: 0 <= k < i + 1 && v == |s[k]|;
    }
  }
}

method SmallestListLengthTest(){
  var s1:seq<seq<int>> := [[1],[1,2]];
  assert |s1| == 2 && |s1[0]| == 1 && |s1[1]| == 2;
  var res1 := SmallestListLength(s1);
  assert res1 == 1;

  var s2:seq<seq<int>> := [[1,2],[1,2,3],[1,2,3,4]];
  assert |s2| == 3 && |s2[0]| == 2 && |s2[1]| == 3 && |s2[2]| == 4;
  var res2:=SmallestListLength(s2);
  assert res2 == 2;

  var s3:seq<seq<int>> := [[3,3,3],[4,4,4,4]];
  assert |s3| == 2 && |s3[0]| == 3 && |s3[1]| == 4;
  var res3:=SmallestListLength(s3);
  assert res3 == 3 ;
}
