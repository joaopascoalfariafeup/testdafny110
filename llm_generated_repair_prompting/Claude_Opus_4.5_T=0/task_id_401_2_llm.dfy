ghost function {:fuel 5} ElementWiseAdditionSpec(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
{
  if |a| == 0 then []
  else ElementWiseAdditionSpec(a[..|a|-1], b[..|b|-1]) + [a[|a|-1] + b[|b|-1]]
}

ghost function {:fuel 5} DeepElementWiseAdditionSpec(a: seq<seq<int>>, b: seq<seq<int>>): seq<seq<int>>
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
{
  if |a| == 0 then []
  else DeepElementWiseAdditionSpec(a[..|a|-1], b[..|b|-1]) + [ElementWiseAdditionSpec(a[|a|-1], b[|a|-1])]
}

method DeepElementWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
  ensures forall i :: 0 <= i < |result| ==> result[i] == ElementWiseAdditionSpec(a[i], b[i])
  ensures result == DeepElementWiseAdditionSpec(a, b)
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> |result[j]| == |a[j]|
    invariant forall j :: 0 <= j < i ==> result[j] == ElementWiseAdditionSpec(a[j], b[j])
    invariant result == DeepElementWiseAdditionSpec(a[..i], b[..i])
  {
    var subResult := ElementWiseAddition(a[i], b[i]);
    assert a[..i+1] == a[..i] + [a[i]];
    assert b[..i+1] == b[..i] + [b[i]];
    assert a[..i+1][|a[..i+1]|-1] == a[i];
    assert b[..i+1][|b[..i+1]|-1] == b[i];
    assert a[..i+1][..|a[..i+1]|-1] == a[..i];
    assert b[..i+1][..|b[..i+1]|-1] == b[..i];
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
  ensures result == ElementWiseAdditionSpec(a, b)
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] + b[j]
    invariant result == ElementWiseAdditionSpec(a[..i], b[..i])
  {
      assert a[..i+1] == a[..i] + [a[i]];
      assert b[..i+1] == b[..i] + [b[i]];
      assert a[..i+1][|a[..i+1]|-1] == a[i];
      assert b[..i+1][|b[..i+1]|-1] == b[i];
      assert a[..i+1][..|a[..i+1]|-1] == a[..i];
      assert b[..i+1][..|b[..i+1]|-1] == b[..i];
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
  // Helper assertions for each element
  assert ElementWiseAdditionSpec([4], [2]) == [6];
  assert ElementWiseAdditionSpec([1, 3], [6, 7]) == [7, 10];
  assert ElementWiseAdditionSpec([2, 9, 1], [1, 1, 8]) == [3, 10, 9];
  assert ElementWiseAdditionSpec([], []) == [];
  // now the full assertion
  assert res1 == [[6], [7, 10], [3, 10, 9], []];
}

