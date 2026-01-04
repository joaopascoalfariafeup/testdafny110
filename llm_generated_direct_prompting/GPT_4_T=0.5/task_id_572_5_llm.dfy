// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..]
  ensures forall k1, k2 :: 0 <= k1 < k2 < |res| ==> res[k1] != res[k2]
  ensures forall k :: 0 <= k < a.Length ==> (exists j :: 0 <= j < |res| && res[j] == a[k]) <==> (forall i :: 0 <= i < k ==> a[i] != a[k])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k1, k2 :: 0 <= k1 < k2 < |res| ==> res[k1] != res[k2]
    invariant forall k :: 0 <= k < i ==> (exists j :: 0 <= j < |res| && res[j] == a[k]) <==> (forall i2 :: 0 <= i2 < k ==> a[i2] != a[k])
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
