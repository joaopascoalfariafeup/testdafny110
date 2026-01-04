// Given two sequences of integers of equal length, checks if the 
// elements in the first sequence are smaller than the elements in the
// second sequence.
predicate AllSmaller(a: seq<int>, b: seq<int>)
  requires |a| == |b|
{
  forall i :: 0 <= i < |a| ==> a[i] < b[i]
}

method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
  requires |a| == |b|
  ensures result == AllSmaller(a, b)
{
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |a| == |b|
    invariant forall k :: 0 <= k < i ==> a[k] < b[k]
  {
    if a[i] >= b[i] {
      assert !AllSmaller(a, b);
      return false;
    }
  }
  return true;
}

method TestIsSmaller(){
  var s1: seq<int> := [2, 3, 4];
  var s2: seq<int> := [1, 2, 3];
  var res1 := IsSmaller(s1, s2);
  assert res1 == false;

  var s3: seq<int> := [3, 4, 5];
  var s4: seq<int> := [4, 5, 6];
  var res2 := IsSmaller(s3, s4);
  assert res2 == true;

  var s5: seq<int> := [1, 2, 4];
  var s6: seq<int> := [2, 3, 4];
  var res3 := IsSmaller(s5, s6);
  assert res3 == false;
}
