// Checks if all sequences in a list of sequences have the same length.
method AllSequencesEqualLength<T>(list: seq<seq<T>>) returns (result: bool)
  ensures result <==> (|list| == 0 || (forall i :: 0 <= i < |list| ==> |list[i]| == |list[0]|))
{
  if |list| == 0 {
    return true;
  }

  var firstLength := |list[0]|;
  var i := 1;
  while i < |list|
    invariant 1 <= i <= |list|
    invariant firstLength == |list[0]|
    invariant forall j :: 0 <= j < i ==> |list[j]| == firstLength
  {
    if |list[i]| != firstLength {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method AllSequencesEqualLengthTest(){
  var s1: seq<seq<int>> := [[11, 22, 33], [44, 55, 66]];
  assert |s1| == 2 && |s1[0]| == 3 && |s1[1]| == 3; // help the verifier with concrete lengths
  var res1 := AllSequencesEqualLength(s1);
  assert res1;

  var s2: seq<seq<int>> := [[1, 2, 3], [4, 5, 6, 7]];
  assert |s2| == 2 && |s2[0]| == 3 && |s2[1]| == 4; // help the verifier with concrete lengths
  var res2 := AllSequencesEqualLength(s2);
  assert !res2;

  var s3: seq<seq<int>> := [[1, 2], [3, 4]];
  assert |s3| == 2 && |s3[0]| == 2 && |s3[1]| == 2; // help the verifier with concrete lengths
  var res3 := AllSequencesEqualLength(s3);
  assert res3;
}
