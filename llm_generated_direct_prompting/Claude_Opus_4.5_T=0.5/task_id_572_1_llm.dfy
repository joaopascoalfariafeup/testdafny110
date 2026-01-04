// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..]
  ensures forall k :: 0 <= k < |res| ==> forall j :: 0 <= j < k ==> res[j] != res[k]
  ensures forall k :: 0 <= k < a.Length ==> a[k] in res
  ensures forall k :: 0 <= k < |res| ==> exists j :: 0 <= j < a.Length && a[j] == res[k] && a[j] !in a[..j]
{
  res := [];
  for i := 0 to a.Length
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k :: 0 <= k < |res| ==> forall j :: 0 <= j < k ==> res[j] != res[k]
    invariant forall k :: 0 <= k < i ==> a[k] in res
    invariant forall k :: 0 <= k < |res| ==> exists j :: 0 <= j < i && a[j] == res[k] && a[j] !in a[..j]
  {
    if a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
}




// Test cases checked statically
method RemoveDuplicatesTest(){
  var a1 := new int[] [1, 2, 1, 2];
  var res1 := RemoveDuplicates(a1);
  assert a1[..] == [1, 2, 1, 2];
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  assert a2[..] == [1, 1, 1];
  assert res2 == [1];
}
