// Returns the index of the *first* longest sublist in a non-empty sequence of lists.
ghost function {:fuel 10} ArgMaxFirst<T>(lists: seq<seq<T>>): int
  requires |lists| > 0
  ensures 0 <= ArgMaxFirst(lists) < |lists|
  ensures forall k :: 0 <= k < |lists| ==> |lists[k]| <= |lists[ArgMaxFirst(lists)]|
  ensures forall k :: 0 <= k < |lists| && |lists[k]| == |lists[ArgMaxFirst(lists)]| ==> ArgMaxFirst(lists) <= k
{
  if |lists| == 1 then
    0
  else
    var j := ArgMaxFirst(lists[..|lists|-1]);
    if |lists[|lists|-1]| > |lists[j]| then |lists|-1 else j
}

// If there is a unique (strict) maximum-length element, ArgMaxFirst must point to it.
lemma UniqueStrictMaxIndex<T>(lists: seq<seq<T>>, m: int)
  requires |lists| > 0
  requires 0 <= m < |lists|
  requires forall k :: 0 <= k < |lists| && k != m ==> |lists[k]| < |lists[m]|
  ensures ArgMaxFirst(lists) == m
{
  var a := ArgMaxFirst(lists);
  if a != m {
    // From maximality of a:
    assert |lists[m]| <= |lists[a]|;
    // From uniqueness of m:
    assert |lists[a]| < |lists[m]|;
    assert false;
  }
}

// Returns the longest list in a non-empty list of lists.
// If there are multiple lists of the same length, the *first* such list is returned.
method MaxLengthSublist<T>(lists: seq<seq<T>>) returns (maxSublist: seq<T>)
  requires |lists| > 0
  ensures maxSublist == lists[ArgMaxFirst(lists)]
  ensures exists j :: 0 <= j < |lists| && maxSublist == lists[j]
  ensures forall k :: 0 <= k < |lists| ==> |lists[k]| <= |maxSublist|
{
  maxSublist := lists[0];
  for i := 1 to |lists|
    invariant 1 <= i <= |lists|
    invariant maxSublist == lists[ArgMaxFirst(lists[..i])]
    invariant exists j :: 0 <= j < i && maxSublist == lists[j]
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
  UniqueStrictMaxIndex(s1, 4);
  var res1 := MaxLengthSublist(s1);
  assert res1 == [13, 15, 17];

  // multiple solutions
  var s2: seq<seq<int>> := [[1], [5, 7], [3, 12]];
  var e2: seq<int> := [10, 12, 14,15];
  var res2 := MaxLengthSublist(s2);

  // Show ArgMaxFirst(s2) cannot be 0 because there exists a longer list (length 2).
  var a := ArgMaxFirst(s2);
  assert |s2[1]| == 2;
  assert |s2[0]| == 1;
  assert |s2[1]| <= |s2[a]|;          // from ArgMaxFirst maximality
  assert |s2[a]| >= 2;
  assert a != 0;
  if a == 1 {
    assert res2 == s2[a];
    assert res2 == [5, 7];
  } else {
    // only remaining possibility is 2
    assert a == 2;
    assert res2 == s2[a];
    assert res2 == [3, 12];
  }
  assert res2 == [5, 7] || res2 == [3, 12]; 
}
