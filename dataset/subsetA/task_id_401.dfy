method DeepElementWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires |a| == |b| 
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> IsElementWiseAddition(a[i], b[i], result[i])
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> IsElementWiseAddition(a[k], b[k], result[k])
  {
    var subResult := ElementWiseAddition(a[i], b[i]);
    result := result + [subResult];
  }
}

// Auxiliary predicate to check if the third sequence (c) if the pairwise 
// addition of the first two sequences of equal size (a and b).
ghost predicate IsElementWiseAddition(a: seq<int>, b: seq<int>, c: seq<int>)
  requires |a| == |b|
{
  |c| == |a| == |b| && forall i :: 0 <= i < |a| ==> c[i] == a[i] + b[i]
}

// Auxiliary method to compute the element wise addition of two sequences of equal size.
method ElementWiseAddition(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b| 
  ensures IsElementWiseAddition(a, b, result)
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
  {
      result := result + [a[i] + b[i]];
  }
}

// Test cases checked statically
method IndexWiseAdditionTest(){
  var s1:seq<seq<int>> :=[[4], [1, 3], [2, 9, 1], []];
  var s2:seq<seq<int>> :=[[2], [6, 7], [1, 1, 8], []];
  var res1 := DeepElementWiseAddition(s1,s2);
  // proof helpers
  assert res1[0] == [6]; // helper
  assert res1[1] == [7, 10]; // helper
  assert res1[2] == [3, 10, 9]; // helper
  assert res1[3] == []; // helper
  // now the full assertion
  assert res1 == [[6], [7, 10], [3, 10, 9], []];
}