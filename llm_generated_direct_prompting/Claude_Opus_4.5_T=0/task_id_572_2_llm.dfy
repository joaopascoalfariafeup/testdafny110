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

ghost function RemoveDuplicatesFunc<T(==)>(s: seq<T>): seq<T>
{
  if |s| == 0 then []
  else if s[|s|-1] in s[..|s|-1] then RemoveDuplicatesFunc(s[..|s|-1])
  else RemoveDuplicatesFunc(s[..|s|-1]) + [s[|s|-1]]
}

// Test cases checked statically
method RemoveDuplicatesTest(){
  var a1 := new int[] [1, 2, 1, 2];
  var res1 := RemoveDuplicates(a1);
  assert a1[..] == [1, 2, 1, 2];
  assert RemoveDuplicatesFunc([1, 2, 1, 2]) == [1, 2];
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  assert a2[..] == [1, 1, 1];
  assert RemoveDuplicatesFunc([1, 1, 1]) == [1];
  assert res2 == [1];
}
