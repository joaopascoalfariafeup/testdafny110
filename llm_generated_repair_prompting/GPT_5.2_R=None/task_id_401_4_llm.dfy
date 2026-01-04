// Ghost helper for element-wise addition
ghost function DeepAdd1(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
  ensures |DeepAdd1(a,b)| == |a|
  ensures forall i :: 0 <= i < |a| ==> DeepAdd1(a,b)[i] == a[i] + b[i]
{
  if |a| == 0 then []
  else DeepAdd1(a[..|a|-1], b[..|b|-1]) + [a[|a|-1] + b[|b|-1]]
}

// Ghost helper that computes deep element-wise addition in an order-preserving way
ghost function DeepAdd(a: seq<seq<int>>, b: seq<seq<int>>): seq<seq<int>>
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures |DeepAdd(a,b)| == |a|
  ensures forall i :: 0 <= i < |a| ==>
            |DeepAdd(a,b)[i]| == |a[i]| &&
            (forall j :: 0 <= j < |a[i]| ==> DeepAdd(a,b)[i][j] == a[i][j] + b[i][j])
{
  if |a| == 0 then []
  else DeepAdd(a[..|a|-1], b[..|b|-1]) + [DeepAdd1(a[|a|-1], b[|b|-1])]
}

// Auxiliary method to compute the element wise addition of two sequences of equal size.
method ElementWiseAddition(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
  ensures result == DeepAdd1(a,b)
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
  {
    result := result + [a[i] + b[i]];
  }
  // Extensionality gives sequence equality from length + pointwise equality
  assert |result| == |DeepAdd1(a,b)|;
  assert forall k :: 0 <= k < |a| ==> result[k] == DeepAdd1(a,b)[k];
}

// Main method
method DeepElementWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==>
            |result[i]| == |a[i]| &&
            (forall j :: 0 <= j < |a[i]| ==> result[i][j] == a[i][j] + b[i][j])
  ensures result == DeepAdd(a,b)
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==>
              |result[k]| == |a[k]| &&
              (forall j :: 0 <= j < |a[k]| ==> result[k][j] == a[k][j] + b[k][j])
  {
    var subResult := ElementWiseAddition(a[i], b[i]);
    result := result + [subResult];
  }
  // Extensionality gives sequence equality from length + pointwise equality
  assert |result| == |DeepAdd(a,b)|;
  assert forall k :: 0 <= k < |a| ==> result[k] == DeepAdd(a,b)[k];
}

// Test cases checked statically
method IndexWiseAdditionTest(){
  var s1:seq<seq<int>> :=[[4], [1, 3], [2, 9, 1], []];
  var s2:seq<seq<int>> :=[[2], [6, 7], [1, 1, 8], []];
  var res1 := DeepElementWiseAddition(s1,s2);

  // Help the prover with concrete unfoldings of DeepAdd on these literals
  assert DeepAdd1([4],[2]) == [6];
  assert DeepAdd1([1,3],[6,7]) == [7,10];
  assert DeepAdd1([2,9,1],[1,1,8]) == [3,10,9];
  assert DeepAdd1([],[]) == [];

  assert DeepAdd(s1,s2)
    == DeepAdd(s1[..|s1|-1], s2[..|s2|-1]) + [DeepAdd1(s1[|s1|-1], s2[|s2|-1])];
  assert DeepAdd(s1[..|s1|-1], s2[..|s2|-1])
    == DeepAdd(s1[..|s1|-2], s2[..|s2|-2]) + [DeepAdd1(s1[|s1|-2], s2[|s2|-2])];
  assert DeepAdd(s1[..|s1|-2], s2[..|s2|-2])
    == DeepAdd(s1[..|s1|-3], s2[..|s2|-3]) + [DeepAdd1(s1[|s1|-3], s2[|s2|-3])];
  assert DeepAdd(s1[..|s1|-3], s2[..|s2|-3])
    == DeepAdd([], []) + [DeepAdd1(s1[0], s2[0])];
  assert DeepAdd([],[]) == [];

  // help the prover connect the expected literal with DeepAdd
  assert res1 == DeepAdd(s1,s2);

  // now the full assertion
  assert res1 == [[6], [7, 10], [3, 10, 9], []];
}
