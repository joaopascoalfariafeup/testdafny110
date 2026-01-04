// Returns the longest list in a non-empty list of lists.
// If there are multiple lists of the same length, any one can be returned.
method MaxLengthSublist<T>(lists: seq<seq<T>>) returns (maxSublist: seq<T>)
  requires |lists| > 0
  ensures exists k :: 0 <= k < |lists| && maxSublist == lists[k]
  ensures forall k :: 0 <= k < |lists| ==> |lists[k]| <= |maxSublist|
{
  maxSublist := lists[0];
  for i := 1 to |lists|
    invariant 1 <= i <= |lists|
    invariant exists k :: 0 <= k < i && maxSublist == lists[k]
    invariant forall k :: 0 <= k < i ==> |lists[k]| <= |maxSublist|
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

  // help the verifier with concrete facts about s1
  assert s1[0] == [0];
  assert s1[1] == [1, 3];
  assert s1[2] == [5, 7];
  assert s1[3] == [9, 11];
  assert s1[4] == [13, 15, 17];
  assert |s1[4]| == 3;
  assert forall k :: 0 <= k < |s1| ==> |s1[k]| <= 3;

  // from postcondition: all sublists have length <= |res1|
  assert forall k :: 0 <= k < |s1| ==> |s1[k]| <= |res1|;
  // in particular, |s1[4]| <= |res1|
  assert |s1[4]| <= |res1|;
  // also, res1 is one of s1's elements, so its length is <= 3
  assert exists k :: 0 <= k < |s1| && res1 == s1[k];
  assert forall k :: 0 <= k < |s1| ==> |s1[k]| <= 3;
  assert |res1| <= 3;
  // hence |res1| == 3
  assert |res1| == 3;

  // only s1[4] has length 3, so res1 must be s1[4]
  assert forall k :: 0 <= k < |s1| && k != 4 ==> |s1[k]| < 3;
  calc {
    res1;
    == { assert res1 == s1[4]; }
    s1[4];
    == [13, 15, 17];
  }
  assert res1 == [13, 15, 17];

  // multiple solutions
  var s2: seq<seq<int>> := [[1], [5, 7], [3, 12]];
  var e2: seq<int> := [10, 12, 14,15];
  var res2 := MaxLengthSublist(s2);

  // help the verifier with concrete facts about s2
  assert s2[0] == [1];
  assert s2[1] == [5, 7];
  assert s2[2] == [3, 12];
  assert |s2[1]| == 2 && |s2[2]| == 2 && |s2[0]| == 1;

  // res2 must be some element of s2, and must have maximal length
  assert exists k :: 0 <= k < |s2| && res2 == s2[k];
  assert forall k :: 0 <= k < |s2| ==> |s2[k]| <= |res2|;

  // maximal length here is 2, so res2 has length 2 and cannot be s2[0]
  assert |res2| == 2;
  assert res2 != s2[0];

  // thus res2 is either s2[1] or s2[2]
  assert res2 == s2[1] || res2 == s2[2];
  assert res2 == [5, 7] || res2 == [3, 12]; 
}
