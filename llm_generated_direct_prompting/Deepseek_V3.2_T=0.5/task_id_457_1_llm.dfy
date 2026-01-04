// Find the shortest sublist in a non-empty list of sublists.
method MinLengthSublist<T>(s: seq<seq<T>>) returns (minSublist: seq<T>)
  requires |s| > 0
  ensures |minSublist| == MinLength(s)
  ensures exists i :: 0 <= i < |s| && minSublist == s[i]
{
  minSublist := s[0];
  for i := 1 to |s|
    invariant 1 <= i <= |s|
    invariant |minSublist| == MinLength(s[..i])
    invariant exists j :: 0 <= j < i && minSublist == s[j]
  {
    if |s[i]| < |minSublist| {
      minSublist := s[i];
    }
  }
}

function MinLength<T>(s: seq<seq<T>>): int
  requires |s| > 0
{
  if |s| == 1 then |s[0]|
  else
    var m := MinLength(s[..|s|-1]);
    if |s[|s|-1]| < m then |s[|s|-1]| else m
}

method MinLengthSublistTest(){
  var s1: seq<seq<int>> := [[1],[1,2],[1,2,3]];
  var res1 := MinLengthSublist(s1);
  assert res1 == s1[0] == [1];

  var s2: seq<seq<int>> := [[1,1],[1,1,1],[1,2,7,8]];
  var res2 := MinLengthSublist(s2);
  assert res2 == s2[0] == [1,1];

  var s3: seq<seq<int>> := [[1,2,3],[3,4],[11,12,14]];
  var res3 := MinLengthSublist(s3);
  assert res3 == s3[1] == [3,4];
}

