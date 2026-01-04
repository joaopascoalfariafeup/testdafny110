// Multiplies the elements of two sequences element-wise.
method ElementWiseMultiplication(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] * b[i]
{
  result := [];
  for i := 0 to |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] * b[k]
  {
    result := result + [a[i] * b[i]];
  }
}

method MultiplyElementsTest(){
  var s1:seq<int> :=[1, 3,4, 5, 2, 9, 1, 10];
  var s2:seq<int> :=[6, 7, 3, 9, 1, 1, 7, 3];
  var res1 := ElementWiseMultiplication(s1,s2);
  assert res1 == [6, 21, 12, 45, 2, 9, 7, 30];
}

