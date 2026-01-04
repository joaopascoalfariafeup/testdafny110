// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == seq(a[..]) where (forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j])
  ensures forall k :: 0 <= k < a.Length ==> a[k] in res
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == seq(a[..i]) where (forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j])
    invariant forall k :: 0 <= k < i ==> a[k] in res
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
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  assert res2 == [1];
}
