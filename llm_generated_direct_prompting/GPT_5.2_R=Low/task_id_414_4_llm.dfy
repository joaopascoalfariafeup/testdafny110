// Checks if two sequences have at least one element in common.
method AnyValueExists<T(==)>(seq1: seq<T>, seq2: seq<T>) returns (result: bool)
  ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
{
  result := false;
  for i := 0 to |seq1|
    invariant 0 <= i <= |seq1|
    invariant result ==> (exists j :: 0 <= j < i && seq1[j] in seq2)
    invariant !result ==> (forall j :: 0 <= j < i ==> !(seq1[j] in seq2))
  {
    if seq1[i] in seq2 {
      result := true;
      return result;
    }
  }
  return result;
}

// Test cases checked statically.
method AnyValueExistsTest(){
  var s1: seq<int> := [1,2,3];
  var s2: seq<int> := [4,5,6];
  var res1 := AnyValueExists(s1, s2);
  assert !res1;

  var s3: seq<int> := [1,4,5];
  var s4: seq<int> := [1,4,5];
  var res2 := AnyValueExists(s3, s4);
  assert res2;

  var s5: seq<int> := [];
  var res3 := AnyValueExists(s5,s5);
  assert !res3;
}
