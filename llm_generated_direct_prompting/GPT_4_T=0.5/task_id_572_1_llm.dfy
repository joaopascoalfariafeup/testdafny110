// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures forall k1, k2 :: 0 <= k1 < k2 < |res| ==> res[k1] != res[k2] // There are no duplicates in the result
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..] // All elements in the result are in the input array
  ensures forall k :: 0 <= k < a.Length ==> a[k] in res // All unique elements in the input array are in the result
{
  res := [];
  for i := 0 to a.Length
    invariant res == a[..i].Distinct()
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
