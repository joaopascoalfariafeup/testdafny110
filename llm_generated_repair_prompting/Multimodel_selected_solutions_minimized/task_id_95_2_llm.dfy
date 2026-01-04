// Finds the length of the shortest list in a non-empty list of lists.

ghost function minLen<T>(s: seq<seq<T>>): int
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && minLen(s) == |s[i]|
  ensures forall i :: 0 <= i < |s| ==> minLen(s) <= |s[i]|
{
  if |s| == 1 then |s[0]|
  else if |s[|s|-1]| < minLen(s[..|s|-1]) then |s[|s|-1]|
  else minLen(s[..|s|-1])
}

method SmallestListLength<T>(s: seq<seq<T>>) returns (v: int)
  requires |s| > 0
  ensures v == minLen(s)
{
  v := |s[0]|;
  for i := 1 to |s|
    invariant v == minLen(s[..i])
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