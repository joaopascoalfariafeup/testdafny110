// Finds the length of the shortest list in a non-empty list of lists.
method SmallestListLength<T>(s: seq<seq<T>>) returns (v: int)
  requires |s| > 0
  ensures 0 <= v
  ensures forall j :: 0 <= j < |s| ==> v <= |s[j]|
  ensures exists j :: 0 <= j < |s| && v == |s[j]|
{
  v := |s[0]|;
  for i := 1 to |s|
    invariant 1 <= i <= |s|
    invariant 0 <= v
    invariant forall j :: 0 <= j < i ==> v <= |s[j]|
    invariant exists j :: 0 <= j < i && v == |s[j]|
  {
    if |s[i]| < v {
      v := |s[i]|;
      assert exists j :: 0 <= j < i + 1 && v == |s[j]|;
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

