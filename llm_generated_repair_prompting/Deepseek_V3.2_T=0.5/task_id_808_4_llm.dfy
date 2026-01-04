// Checks if a sequence 's' contains a value 'x'.
method Contains<T(==)>(s: seq<T>, x: T) returns (result: bool)
  ensures result == (exists i :: 0 <= i < |s| && s[i] == x)
{
  result := false;
  for i := 0 to |s|
    invariant result == (exists k :: 0 <= k < i && s[k] == x)
    invariant i >= 0 && i <= |s|
  {
    if i < |s| && s[i] == x {
      result := true;
      return;
    }
  }
}

// Test cases checked statically
method ContainsTest(){
  var s1: seq<int> := [10, 4, 5, 6, 8];
  var res1 := Contains(s1,6);
  // Helper assertion to trigger verification
  assert s1[3] == 6;
  assert res1;

  var s2: seq<int> := [1, 2, 3, 4, 5, 6];
  var res2 := Contains(s2, 7);
  assert !res2;

  var s3: seq<char> := ['a', 'c', 'd'];
  var res3:=Contains(s3, 'c');
  // Helper assertion to trigger verification
  assert s3[1] == 'c';
  assert res3;
}



