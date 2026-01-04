ghost predicate SameShape(a: seq<seq<int>>, b: seq<seq<int>>)
{
  |a| == |b| && (forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|)
}

ghost function ElementWiseSum(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
{
  seq(i | 0 <= i < |a| :: a[i] + b[i])
}

ghost function DeepElementWiseSum(a: seq<seq<int>>, b: seq<seq<int>>): seq<seq<int>>
  requires SameShape(a, b)
{
  seq(i | 0 <= i < |a| :: ElementWiseSum(a[i], b[i]))
}

method DeepElementWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires SameShape(a, b)
  ensures |result| == |a|
  ensures result == DeepElementWiseSum(a, b)
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == ElementWiseSum(a[j], b[j])
  {
    var subResult := ElementWiseAddition(a[i], b[i]);
    result := result + [subResult];
  }
}


// Auxiliary method to compute the element wise addition of two sequences of equal size.
method ElementWiseAddition(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures result == ElementWiseSum(a, b)
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] + b[j]
  {
      result := result + [a[i] + b[i]];
  }
}

// Test cases checked statically
method IndexWiseAdditionTest(){
  var s1:seq<seq<int>> :=[[4], [1, 3], [2, 9, 1], []];
  var s2:seq<seq<int>> :=[[2], [6, 7], [1, 1, 8], []];
  var res1 := DeepElementWiseAddition(s1,s2);
  // now the full assertion
  assert res1 == [[6], [7, 10], [3, 10, 9], []];
}
