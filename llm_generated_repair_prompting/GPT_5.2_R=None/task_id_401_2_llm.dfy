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

// Ghost helper for element-wise addition
ghost function DeepAdd1(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
  ensures |DeepAdd1(a,b)| == |a|
  ensures forall i :: 0 <= i < |a| ==> DeepAdd1(a,b)[i] == a[i] + b[i]
{
  if |a| == 0 then []
  else DeepAdd1(a[..|a|-1], b[..|b|-1]) + [a[|a|-1] + b[|b|-1]]
}

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
    invariant result == DeepAdd(a[..i], b[..i])
  {
    var subResult := ElementWiseAddition(a[i], b[i]);
    result := result + [subResult];
    assert a[..i+1] == a[..i] + [a[i]];
    assert b[..i+1] == b[..i] + [b[i]];
  }
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
    invariant result == DeepAdd1(a[..i], b[..i])
  {
      result := result + [a[i] + b[i]];
      assert a[..i+1] == a[..i] + [a[i]];
      assert b[..i+1] == b[..i] + [b[i]];
  }
}

// Test cases checked statically
method IndexWiseAdditionTest(){
  var s1:seq<seq<int>> :=[[4], [1, 3], [2, 9, 1], []];
  var s2:seq<seq<int>> :=[[2], [6, 7], [1, 1, 8], []];
  var res1 := DeepElementWiseAddition(s1,s2);
  // help the prover connect the expected literal with DeepAdd
  assert res1 == DeepAdd(s1,s2);
  // now the full assertion
  assert res1 == [[6], [7, 10], [3, 10, 9], []];
}
