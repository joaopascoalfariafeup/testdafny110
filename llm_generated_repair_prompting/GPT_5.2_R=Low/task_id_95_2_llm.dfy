// Finds the length of the shortest list in a non-empty list of lists.
method SmallestListLength<T>(s: seq<seq<T>>) returns (v: int)
  requires |s| > 0
  ensures 0 <= v
  ensures forall j :: 0 <= j < |s| ==> v <= |s[j]|
  ensures exists j :: 0 <= j < |s| && v == |s[j]|
{
  v := |s[0]|;
  for i := 1 to |s|
    invariant 1 <= i <= |s|
    invariant 0 <= v
    invariant forall j :: 0 <= j < i ==> v <= |s[j]|
    invariant exists j :: 0 <= j < i && v == |s[j]|
  {
    if |s[i]| < v {
      v := |s[i]|;
      assert exists j :: 0 <= j < i + 1 && v == |s[j]|;
    }
  }
}

method SmallestListLengthTest(){
  var s1:seq<seq<int>> := [[1],[1,2]];
  assert |s1| == 2;
  assert |s1[0]| == 1;
  assert |s1[1]| == 2;
  var res1 := SmallestListLength(s1);

  // Use the postcondition witness + bounds to pin down the exact value.
  var j1 :| 0 <= j1 < |s1| && res1 == |s1[j1]|;
  assert res1 <= |s1[0]|; // so res1 <= 1
  if j1 == 0 {
    assert res1 == 1;
  } else {
    assert j1 == 1;
    assert res1 == 2;
    assert false; // contradicts res1 <= 1
  }
  assert res1 == 1;

  var s2:seq<seq<int>> := [[1,2],[1,2,3],[1,2,3,4]];
  assert |s2| == 3;
  assert |s2[0]| == 2;
  assert |s2[1]| == 3;
  assert |s2[2]| == 4;
  var res2:=SmallestListLength(s2);

  var j2 :| 0 <= j2 < |s2| && res2 == |s2[j2]|;
  assert res2 <= |s2[0]|; // so res2 <= 2
  if j2 == 0 {
    assert res2 == 2;
  } else {
    // j2 == 1 or 2 implies res2 is 3 or 4, impossible since res2 <= 2
    if j2 == 1 {
      assert res2 == 3;
      assert false;
    } else {
      assert j2 == 2;
      assert res2 == 4;
      assert false;
    }
  }
  assert res2 == 2;

  var s3:seq<seq<int>> := [[3,3,3],[4,4,4,4]];
  assert |s3| == 2;
  assert |s3[0]| == 3;
  assert |s3[1]| == 4;
  var res3:=SmallestListLength(s3);

  var j3 :| 0 <= j3 < |s3| && res3 == |s3[j3]|;
  assert res3 <= |s3[0]|; // so res3 <= 3
  if j3 == 0 {
    assert res3 == 3;
  } else {
    assert j3 == 1;
    assert res3 == 4;
    assert false; // contradicts res3 <= 3
  }
  assert res3 == 3 ;
}
