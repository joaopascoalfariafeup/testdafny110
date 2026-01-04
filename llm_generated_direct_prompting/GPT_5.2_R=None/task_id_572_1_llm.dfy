// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures forall i :: 0 <= i < |res| ==> res[i] in a[..a.Length]
  ensures forall x :: x in a[..a.Length] ==> x in res
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall x, y :: x in a[..a.Length] && y in a[..a.Length] &&
                       (exists ix, iy :: 0 <= ix < iy < a.Length && a[ix] == x && a[iy] == y) &&
                       !(exists iy, ix :: 0 <= iy < ix < a.Length && a[iy] == y && a[ix] == x)
                       ==> (exists rx, ry :: 0 <= rx < ry < |res| && res[rx] == x && res[ry] == y)
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < |res| ==> res[j] in a[..i]
    invariant forall x :: x in a[..i] ==> x in res
    invariant forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
    invariant forall x, y :: x in a[..i] && y in a[..i] &&
                         (exists ix, iy :: 0 <= ix < iy < i && a[ix] == x && a[iy] == y) &&
                         !(exists iy, ix :: 0 <= iy < ix < i && a[iy] == y && a[ix] == x)
                         ==> (exists rx, ry :: 0 <= rx < ry < |res| && res[rx] == x && res[ry] == y)
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
