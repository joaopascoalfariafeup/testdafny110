ghost function ElementWiseAdditionFunc(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
{
  if |a| == 0 then []
  else ElementWiseAdditionFunc(a[..|a|-1], b[..|b|-1]) + [a[|a|-1] + b[|b|-1]]
}

ghost function DeepElementWiseAdditionFunc(a: seq<seq<int>>, b: seq<seq<int>>): seq<seq<int>>
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
{
  if |a| == 0 then []
  else DeepElementWiseAdditionFunc(a[..|a|-1], b[..|b|-1]) + [ElementWiseAdditionFunc(a[|a|-1], b[|a|-1])]
}

method DeepElementWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
  ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
  ensures result == DeepElementWiseAdditionFunc(a, b)
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |a[k]|
    invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < |result[k]| ==> result[k][j] == a[k][j] + b[k][j]
    invariant forall k :: 0 <= k < i ==> result[k] == ElementWiseAdditionFunc(a[k], b[k])
    invariant result == DeepElementWiseAdditionFunc(a[..i], b[..i])
  {
    var subResult := ElementWiseAddition(a[i], b[i]);
    result := result + [subResult];
  }
  assert a[..|a|] == a;
  assert b[..|b|] == b;
}


// Auxiliary method to compute the element wise addition of two sequences of equal size.
method ElementWiseAddition(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
  ensures result == ElementWiseAdditionFunc(a, b)
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
    invariant result == ElementWiseAdditionFunc(a[..i], b[..i])
  {
      result := result + [a[i] + b[i]];
  }
  assert a[..|a|] == a;
  assert b[..|b|] == b;
}

// Test cases checked statically
method IndexWiseAdditionTest(){
  var s1:seq<seq<int>> :=[[4], [1, 3], [2, 9, 1], []];
  var s2:seq<seq<int>> :=[[2], [6, 7], [1, 1, 8], []];
  var res1 := DeepElementWiseAddition(s1,s2);
  // now the full assertion
  assert res1 == [[6], [7, 10], [3, 10, 9], []];
}
