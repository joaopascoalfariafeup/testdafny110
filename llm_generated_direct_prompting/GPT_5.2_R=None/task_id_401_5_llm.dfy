method DeepElementWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==>
            |result[i]| == |a[i]| &&
            (forall j :: 0 <= j < |a[i]| ==> result[i][j] == a[i][j] + b[i][j])
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |a| == |b|
    invariant forall k :: 0 <= k < |a| ==> |a[k]| == |b[k]|
    invariant |result| == i
    invariant forall r :: 0 <= r < i ==>
              |result[r]| == |a[r]| &&
              (forall c :: 0 <= c < |a[r]| ==> result[r][c] == a[r][c] + b[r][c])
  {
    var subResult := ElementWiseAddition(a[i], b[i]);
    result := result + [subResult];
  }
}


// Auxiliary method to compute the element wise addition of two sequences of equal size.
method ElementWiseAddition(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |a| == |b|
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
  // now the full assertion
  assert res1 == [[6], [7, 10], [3, 10, 9], []];
}
