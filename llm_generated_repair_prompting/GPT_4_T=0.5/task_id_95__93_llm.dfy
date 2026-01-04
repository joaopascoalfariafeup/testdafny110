// Finds the length of the shortest list in a non-empty list of lists.
method SmallestListLength<T>(s: seq<seq<T>>) returns (v: int)
  requires |s| > 0
  ensures v >= 0
  ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
  ensures exists i :: 0 <= i < |s| && v == |s[i]|
{
  v := |s[0]|;
  for i := 1 to |s|
    invariant 0 <= i <= |s|
    invariant v >= 0
    invariant forall j :: 0 <= j < i ==> v <= |s[j]|
    invariant exists j :: 0 <= j < i && v == |s[j]|
    invariant v == min(seqc(s[..i], x => true, y => |y|))
  {
    if |s[i]| < v {
      v := |s[i]|;
    }
  }
}

ghost function seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U> 
{
  if s == [] then []
  else if f(s[0]) then [g(s[0])] + seqc(s[1..], f, g)
  else seqc(s[1..], f, g)
}

ghost function {:fuel 5} min(s: seq<int>): int
  requires |s| > 0
  ensures min(s) in s && forall k :: 0 <= k < |s| ==> s[k] >= min(s)
{ 
  if |s| == 1 then s[0] else if s[0] < min(s[1..]) then s[0] else min(s[1..])
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

