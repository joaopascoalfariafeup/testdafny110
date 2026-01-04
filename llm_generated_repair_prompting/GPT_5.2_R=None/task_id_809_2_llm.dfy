// Given two sequences of integers of equal length, checks if the
// elements in the first sequence are smaller than the elements in the
// second sequence.
method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
  requires |a| == |b|
  ensures result <==> (forall i :: 0 <= i < |a| ==> a[i] < b[i])
{
  var foundBad := false;

  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant foundBad ==> (exists j :: 0 <= j < i && a[j] >= b[j])
    invariant !foundBad ==> (forall j :: 0 <= j < i ==> a[j] < b[j])
  {
    if a[i] >= b[i] {
      foundBad := true;
      return false;
    }
  }
  return true;
}

method TestIsSmaller(){
  var s1: seq<int> := [2, 3, 4];
  var s2: seq<int> := [1, 2, 3];
  assert s1[0] >= s2[0];
  var res1 := IsSmaller(s1, s2);
  assert res1 == false;

  var s3: seq<int> := [3, 4, 5];
  var s4: seq<int> := [4, 5, 6];
  var res2 := IsSmaller(s3, s4);
  assert res2 == true;

  var s5: seq<int> := [1, 2, 4];
  var s6: seq<int> := [2, 3, 4];
  assert s5[2] >= s6[2];
  var res3 := IsSmaller(s5, s6);
  assert res3 == false;
}
