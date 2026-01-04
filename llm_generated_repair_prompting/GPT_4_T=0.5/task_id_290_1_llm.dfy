// Returns the longest list in a non-empty list of lists.
// If there are multiple lists of the same length, any one can be returned.
method MaxLengthSublist<T>(lists: seq<seq<T>>) returns (maxSublist: seq<T>)
  requires |lists| > 0
  ensures forall k :: 0 <= k < |lists| ==> |maxSublist| >= |lists[k]|
  ensures exists k :: 0 <= k < |lists| && |maxSublist| == |lists[k]|
{
  maxSublist := lists[0];
  for i := 1 to |lists|
    invariant 0 <= i <= |lists|
    invariant forall k :: 0 <= k < i ==> |maxSublist| >= |lists[k]|
    invariant exists k :: 0 <= k < i && |maxSublist| == |lists[k]|
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
  assert res1 == [13, 15, 17];

  // multiple solutions
  var s2: seq<seq<int>> := [[1], [5, 7], [3, 12]];
  var e2: seq<int> := [10, 12, 14,15];
  var res2 := MaxLengthSublist(s2);
  assert res2 == [5, 7] || res2 == [3, 12]; 
}

