// Returns the longest list in a non-empty list of lists.
// If there are multiple lists of the same length, any one can be returned.
method MaxLengthSublist<T>(lists: seq<seq<T>>) returns (maxSublist: seq<T>)
  requires |lists| > 0
  ensures maxSublist in lists
  ensures forall i :: 0 <= i < |lists| ==> |lists[i]| <= |maxSublist|
{
  maxSublist := lists[0];
  for i := 1 to |lists|
    invariant maxSublist in lists
    invariant forall j :: 0 <= j < i ==> |lists[j]| <= |maxSublist|
  {
    if |lists[i]| > |maxSublist| {
      maxSublist := lists[i];
    }
  }
}

method MaxLengthListTest(){
  // typical case
  var s1: seq<seq<int>> := [[0], [1, 3], [5, 7], [9, 11], [13, 15, 17]];
  var res1 := MaxLengthSublist(s1);
  // Helper assertions to show [13, 15, 17] is the unique longest
  assert s1[0] == [0] && |s1[0]| == 1;
  assert s1[1] == [1, 3] && |s1[1]| == 2;
  assert s1[2] == [5, 7] && |s1[2]| == 2;
  assert s1[3] == [9, 11] && |s1[3]| == 2;
  assert s1[4] == [13, 15, 17] && |s1[4]| == 3;
  // res1 is in s1 and has length >= 3, so it must be [13, 15, 17]
  assert |res1| >= 3;
  assert res1 in s1;
  assert res1 == s1[0] || res1 == s1[1] || res1 == s1[2] || res1 == s1[3] || res1 == s1[4];
  assert res1 == [13, 15, 17];

  // multiple solutions
  var s2: seq<seq<int>> := [[1], [5, 7], [3, 12]];
  var e2: seq<int> := [10, 12, 14,15];
  var res2 := MaxLengthSublist(s2);
  // Helper assertions
  assert s2[0] == [1] && |s2[0]| == 1;
  assert s2[1] == [5, 7] && |s2[1]| == 2;
  assert s2[2] == [3, 12] && |s2[2]| == 2;
  assert |res2| >= 2;
  assert res2 in s2;
  assert res2 == s2[0] || res2 == s2[1] || res2 == s2[2];
  assert res2 == [5, 7] || res2 == [3, 12]; 
}
