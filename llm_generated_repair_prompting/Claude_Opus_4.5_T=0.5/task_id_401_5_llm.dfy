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
  
  // Helper assertions to unfold DeepElementWiseAdditionSpec step by step
  assert DeepElementWiseAdditionSpec([], []) == [];
  
  // Build up step by step using local variables to help Dafny
  var a1: seq<seq<int>> := [[4]];
  var b1: seq<seq<int>> := [[2]];
  assert a1[..0] == [];
  assert b1[..0] == [];
  assert a1[0] == [4];
  assert b1[0] == [2];
  assert DeepElementWiseAdditionSpec(a1, b1) == DeepElementWiseAdditionSpec([], []) + [ElementWiseAdditionSpec([4], [2])];
  assert DeepElementWiseAdditionSpec(a1, b1) == [[6]];
  
  var a2: seq<seq<int>> := [[4], [1, 3]];
  var b2: seq<seq<int>> := [[2], [6, 7]];
  assert a2[..1] == [[4]];
  assert b2[..1] == [[2]];
  assert DeepElementWiseAdditionSpec(a2, b2) == [[6], [7, 10]];
  
  var a3: seq<seq<int>> := [[4], [1, 3], [2, 9, 1]];
  var b3: seq<seq<int>> := [[2], [6, 7], [1, 1, 8]];
  assert a3[..2] == [[4], [1, 3]];
  assert b3[..2] == [[2], [6, 7]];
  assert DeepElementWiseAdditionSpec(a3, b3) == [[6], [7, 10], [3, 10, 9]];
  
  assert s1[..3] == [[4], [1, 3], [2, 9, 1]];
  assert s2[..3] == [[2], [6, 7], [1, 1, 8]];
  assert DeepElementWiseAdditionSpec(s1, s2) == [[6], [7, 10], [3, 10, 9], []];
  
  // now the full assertion
  assert res1 == [[6], [7, 10], [3, 10, 9], []];
}

