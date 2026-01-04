// Adds two lists element wise and returns the resulting list.
method ElementWiseAddition(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b| // Both lists should have the same size
  ensures |result| == |a| // The result list should have the same size as the input lists
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i] // Each element in the result list should be the sum of the corresponding elements in the input lists
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i // The size of the result list after each iteration equals the current iteration index
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k] // Each element in the result list up to the current index is the sum of the corresponding elements in the input lists
  {
    result := result + [a[i] + b[i]];
  }
}

// Test cases checked statically
method AddListsTest(){
  var a1: seq<int>:=[10, 20, 30];
  var a2: seq<int>:= [15, 25, 35];
  var res1 := ElementWiseAddition(a1, a2);
  assert res1 == [25, 45, 65];

  var a3: seq<int>:= [1, 2, 3];
  var a4: seq<int>:= [5, 6, 7];
  var res2 := ElementWiseAddition(a3, a4);
  assert res2 == [6, 8, 10];
}
