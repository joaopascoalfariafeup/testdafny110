// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures forall k1, k2 :: 0 <= k1 < k2 < |res| ==> res[k1] != res[k2] // No duplicates in the result
  ensures forall k1 :: 0 <= k1 < |res| ==> res[k1] in a[..] // All elements in the result are in the original array
  ensures forall k1 :: 0 <= k1 < a.Length ==> a[k1] in res // All elements in the original array are in the result
{
  res := [];
  for i := 0 to a.Length
    invariant res == a[..i].Distinct() // The result is the sequence of distinct elements up to the current index
    invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> a[k1] != a[k2] // No duplicates up to the current index
    invariant forall k1 :: 0 <= k1 < i ==> a[k1] in res // All elements up to the current index are in the result
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
