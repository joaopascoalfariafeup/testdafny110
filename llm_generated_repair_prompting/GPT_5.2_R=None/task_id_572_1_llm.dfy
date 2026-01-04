// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures forall i :: 0 <= i < |res| ==> res[i] in a[..a.Length]
  ensures forall i,j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < a.Length ==> a[i] in res
  ensures forall x :: x in a[..a.Length] ==> x in res
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall p,q :: 0 <= p < q < |res| ==> res[p] != res[q]
    invariant forall j :: 0 <= j < i ==> a[j] in res
    invariant forall x :: x in a[..i] ==> x in res
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
