// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures forall x :: x in res ==> x in a[..] && x in b[..]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall x :: x in a[..] && x in b[..] ==> x in res
  ensures forall i, j :: 0 <= i < j < |res| ==>
            (exists ia, ja :: 0 <= ia < ja < a.Length && a[ia] == res[i] && a[ja] == res[j])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in res ==> x in a[..i] && x in b[..]
    invariant forall ii, jj :: 0 <= ii < jj < |res| ==> res[ii] != res[jj]
    invariant forall x :: x in a[..i] && x in b[..] ==> x in res
    invariant forall ii, jj :: 0 <= ii < jj < |res| ==>
              (exists ia, ja :: 0 <= ia < ja < i && a[ia] == res[ii] && a[ja] == res[jj])
  {
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      res := res + [a[i]];
    }
  }
}

// Test cases checked statically
method IntersectionTest(){
  var a := new int[] [1, 2, 3];
  var b := new int[] [1, 3, 1];
  var c := new int[] [2, 4, 6];

  // Typical case
  var res1 := Intersection(a, b);
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert res3 == [1, 3] || res3 == [3, 1];
}
