// Checks if a sequence 's' contains a value 'x'.
method Contains<T(==)>(s: seq<T>, x: T) returns (result: bool)
  ensures result <==> (exists i :: 0 <= i < |s| && s[i] == x)
{
  result := false;

  // Handle empty sequence explicitly
  if |s| == 0 {
    return false;
  }

  // Iterate over valid indices 0 .. |s|-1
  for i := 0 to |s|-1
    invariant 0 <= i <= |s|
    invariant result <==> (exists j :: 0 <= j < i && s[j] == x)
    invariant !result ==> (forall j :: 0 <= j < i ==> s[j] != x)
  {
    if s[i] == x {
      return true;
    }
  }

  // If we reached here, no index had s[i] == x.
  // At loop end, i == |s|, and result is still false.
  assert !result;
  // Use the loop invariant instantiated with i == |s| to lift to the full range.
  assert forall j :: 0 <= j < |s| ==> s[j] != x;
  assert !(exists j :: 0 <= j < |s| && s[j] == x);
  return false;
}

// Test cases checked statically
method ContainsTest(){
  var s1: seq<int> := [10, 4, 5, 6, 8];
  assert s1[3] == 6;
  assert (exists i :: 0 <= i < |s1| && s1[i] == 6);
  var res1 := Contains(s1,6);
  assert res1;

  var s2: seq<int> := [1, 2, 3, 4, 5, 6];
  assert !(exists i :: 0 <= i < |s2| && s2[i] == 7);
  var res2 := Contains(s2, 7);
  assert !res2;

  var s3: seq<char> := ['a', 'c', 'd'];
  assert s3[1] == 'c';
  assert (exists i :: 0 <= i < |s3| && s3[i] == 'c');
  var res3:=Contains(s3, 'c');
  assert res3;
}
