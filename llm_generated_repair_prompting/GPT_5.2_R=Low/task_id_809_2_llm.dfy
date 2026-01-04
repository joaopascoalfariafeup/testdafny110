// Given two sequences of integers of equal length, checks if the 
// elements in the first sequence are smaller than the elements in the
// second sequence.
method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
  requires |a| == |b|
  ensures result <==> (forall i :: 0 <= i < |a| ==> a[i] < b[i])
{
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> a[j] < b[j]
  {
    if a[i] >= b[i] {
      return false;
    }
  }
  return true;
}

method TestIsSmaller(){
  var s1: seq<int> := [2, 3, 4];
  var s2: seq<int> := [1, 2, 3];
  var res1 := IsSmaller(s1, s2);

  // Help Dafny prove res1 is false by exhibiting a counterexample index
  assert |s1| == 3 && |s2| == 3;
  assert 0 <= 0 < |s1|;
  assert s1[0] == 2 && s2[0] == 1;
  assert s1[0] >= s2[0];
  assert !(s1[0] < s2[0]);
  assert !(forall i :: 0 <= i < |s1| ==> s1[i] < s2[i]);
  assert res1 == false;

  var s3: seq<int> := [3, 4, 5];
  var s4: seq<int> := [4, 5, 6];
  var res2 := IsSmaller(s3, s4);
  assert res2 == true;

  var s5: seq<int> := [1, 2, 4];
  var s6: seq<int> := [2, 3, 4];
  var res3 := IsSmaller(s5, s6);

  // Help Dafny prove res3 is false by exhibiting a counterexample index
  assert |s5| == 3 && |s6| == 3;
  assert 0 <= 2 < |s5|;
  assert s5[2] == 4 && s6[2] == 4;
  assert s5[2] >= s6[2];
  assert !(s5[2] < s6[2]);
  assert !(forall i :: 0 <= i < |s5| ==> s5[i] < s6[i]);
  assert res3 == false;
}
