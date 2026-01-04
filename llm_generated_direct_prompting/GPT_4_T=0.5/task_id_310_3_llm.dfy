// Converts a string (sequence of characters) to an array of characters.
method ToCharArray(s: string) returns (a: array<char>)
  ensures a != null && |a| == |s| && forall k :: 0 <= k < |s| ==> a[k] == s[k]
{
  a := new char[|s|];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> a[k] == s[k]
  {
    a[i] := s[i];
  }
}

// Test cases checked statically.
method ToCharArrayTest(){
  var e1: seq<char> := ['p', 'y', 't', 'h', 'o', 'n',' ','3', '.', '0'];
  var res1 := ToCharArray("python 3.0");
  assert res1[..] == ['p','y','t','h','o','n',' ','3','.','0'];

  var e2: seq<char> := ['i', 't', 'e', 'm', '1'];
  var res2:=ToCharArray("item1");
  assert res2[..] == ['i','t','e','m','1'];

  var e3: seq<char> := ['1', '5', '.', '1', '0'];
  var res3:=ToCharArray("15.10");
  assert res3[..] == ['1','5','.','1','0'];
}
