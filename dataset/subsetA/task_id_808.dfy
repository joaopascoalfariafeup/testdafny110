// Checks if a sequence 's' contains a value 'x'.
method Contains<T(==)>(s: seq<T>, x: T) returns (result: bool)
  ensures result <==> x in s
{
  result := false;
  for i := 0 to |s|
    invariant x !in s[..i]
  {
    if s[i] == x {
      return true;
    }
  }
  return false;
}

// Test cases checked statically
method ContainsTest(){
  var s1: seq<int> := [10, 4, 5, 6, 8];
  var res1 := Contains(s1,6);
  assert res1;

  var s2: seq<int> := [1, 2, 3, 4, 5, 6];
  var res2 := Contains(s2, 7);
  assert !res2;

  var s3: seq<char> := ['a', 'c', 'd'];
  var res3:=Contains(s3, 'c');
  assert res3;
}

