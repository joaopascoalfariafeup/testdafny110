// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..]
  ensures forall k :: 0 <= k < a.Length && a[k] !in a[..k] ==> a[k] in res
  ensures forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
  ensures forall k :: 0 <= k < |res| ==> res[k] !in res[..k]
  ensures res == RemoveDuplicatesFunc(a[..])
{
  res := [];
  for i := 0 to a.Length
    invariant res == RemoveDuplicatesFunc(a[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    if a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
  assert a[..a.Length] == a[..];
}

ghost function {:fuel 5} RemoveDuplicatesFunc<T>(s: seq<T>): seq<T>
  ensures forall k :: 0 <= k < |RemoveDuplicatesFunc(s)| ==> RemoveDuplicatesFunc(s)[k] in s
  ensures forall k :: 0 <= k < |s| && s[k] !in s[..k] ==> s[k] in RemoveDuplicatesFunc(s)
  ensures forall j, k :: 0 <= j < k < |RemoveDuplicatesFunc(s)| ==> RemoveDuplicatesFunc(s)[j] != RemoveDuplicatesFunc(s)[k]
  ensures forall k :: 0 <= k < |RemoveDuplicatesFunc(s)| ==> RemoveDuplicatesFunc(s)[k] !in RemoveDuplicatesFunc(s)[..k]
{
  if |s| == 0 then []
  else 
    var prev := RemoveDuplicatesFunc(s[..|s|-1]);
    if s[|s|-1] in s[..|s|-1] then prev
    else prev + [s[|s|-1]]
}

// Test cases checked statically
method RemoveDuplicatesTest(){
  var a1 := new int[] [1, 2, 1, 2];
  var res1 := RemoveDuplicates(a1);
  assert a1[..] == [1, 2, 1, 2];
  // Help Dafny compute the function step by step
  var empty: seq<int> := [];
  assert [1, 2, 1, 2][..0] == empty;
  assert RemoveDuplicatesFunc(empty) == empty;
  assert [1, 2, 1, 2][..1] == [1];
  assert RemoveDuplicatesFunc([1]) == [1];
  assert [1, 2, 1, 2][..2] == [1, 2];
  assert RemoveDuplicatesFunc([1, 2]) == [1, 2];
  assert [1, 2, 1, 2][..3] == [1, 2, 1];
  assert 1 in [1, 2];
  assert RemoveDuplicatesFunc([1, 2, 1]) == [1, 2];
  assert 2 in [1, 2, 1];
  assert RemoveDuplicatesFunc([1, 2, 1, 2]) == [1, 2];
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  assert a2[..] == [1, 1, 1];
  assert RemoveDuplicatesFunc([1]) == [1];
  assert 1 in [1];
  assert RemoveDuplicatesFunc([1, 1]) == [1];
  assert 1 in [1, 1];
  assert RemoveDuplicatesFunc([1, 1, 1]) == [1];
  assert res2 == [1];
}

