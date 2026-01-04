// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res.Length <= a.Length
  ensures forall k :: 0 <= k < res.Length ==> res[k] in a[..]
  ensures forall k :: 0 <= k < res.Length ==> (res[k] !in res[..k])
  ensures forall k :: 0 <= k < a.Length ==> (a[k] in res[..])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res.Length <= i
    invariant forall k :: 0 <= k < i ==> (a[k] in res[..]) 
    invariant forall k :: 0 <= k < res.Length ==> (res[k] in a[..k]) 
    invariant forall k :: 0 <= k < res.Length ==> (res[k] !in res[..k]) 
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
