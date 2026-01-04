// Returns a sequence with the last character of each string in the input list.
method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
  requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == Last(l[i])
{
  r := [];
  for i := 0 to |l|
    invariant |r| == i
    invariant forall k :: 0 <= k < i ==> r[k] == Last(l[k])
  {
    r := r + [Last(l[i])];
  }
}

// Auxiliary function to get the last element of a non-empty sequence.
function Last<T>(s: seq<T>): T
  requires |s| > 0
{
  s[|s| - 1]
}

// Test cases checked statically.
method ExtractRearCharsTest(){
  var s1: seq<string> := ["Mers", "for", "Vers"];
  var res1 := ExtractRearChars(s1);
  assert res1 == ['s', 'r', 's'];

  var s2: seq<string> := ["Avenge", "for", "People"];
  var res2:=ExtractRearChars(s2);
  assert res2 == ['e', 'r', 'e'];

  var s3: seq<string> := ["a", "b", "c"];
  var res3 := ExtractRearChars(s3);
  assert res3 == ['a', 'b', 'c'];
}