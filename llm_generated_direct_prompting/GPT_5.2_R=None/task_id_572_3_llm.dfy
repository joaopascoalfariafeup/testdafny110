// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..a.Length]
  ensures forall k :: 0 <= k < |res| ==> res[k] !in res[..k]
  ensures forall i :: 0 <= i < a.Length ==> (a[i] !in a[..i] <==> a[i] in res)
  ensures forall x :: x in res ==> exists i :: 0 <= i < a.Length && a[i] == x && x !in a[..i]
{
  res := [];
  for i := 0 to a.Length
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k :: 0 <= k < |res| ==> res[k] !in res[..k]
    invariant forall j :: 0 <= j < i ==> (a[j] !in a[..j] <==> a[j] in res)
    invariant forall x :: x in res ==> exists j :: 0 <= j < i && a[j] == x && x !in a[..j]
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
