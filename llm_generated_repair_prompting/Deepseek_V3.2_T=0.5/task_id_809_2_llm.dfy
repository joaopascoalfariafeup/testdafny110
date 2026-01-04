// Given two sequences of integers of equal length, checks if the 
// elements in the first sequence are smaller than the elements in the
// second sequence.
method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
  requires |a| == |b|
  ensures result == (forall i | 0 <= i < |a| :: a[i] < b[i])
{
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j | 0 <= j < i :: a[j] < b[j]
  {
    if a[i] >= b[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method TestIsSmaller(){
  var s1: seq<int> := [2, 3, 4];
  var s2: seq<int> := [1, 2, 3];
  var res1 := IsSmaller(s1, s2);
  // Helper assertions to verify the test
  assert s1[0] == 2 && s1[1] == 3 && s1[2] == 4;
  assert s2[0] == 1 && s2[1] == 2 && s2[2] == 3;
  assert s1[0] >= s2[0]; // 2 >= 1
  assert res1 == false;

  var s3: seq<int> := [3, 4, 5];
  var s4: seq<int> := [4, 5, 6];
  var res2 := IsSmaller(s3, s4);
  // Helper assertions
  assert s3[0] == 3 && s3[1] == 4 && s3[2] == 5;
  assert s4[0] == 4 && s4[1] == 5 && s4[2] == 6;
  assert s3[0] < s4[0] && s3[1] < s4[1] && s3[2] < s4[2];
  assert res2 == true;

  var s5: seq<int> := [1, 2, 4];
  var s6: seq<int> := [2, 3, 4];
  var res3 := IsSmaller(s5, s6);
  // Helper assertions
  assert s5[0] == 1 && s5[1] == 2 && s5[2] == 4;
  assert s6[0] == 2 && s6[1] == 3 && s6[2] == 4;
  assert s5[2] >= s6[2]; // 4 >= 4
  assert res3 == false;
}

