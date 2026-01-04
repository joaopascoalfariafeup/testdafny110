// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures forall x: T :: x in res <==> (x in a[..] && x in b[..])
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < |res| ==> (exists k :: 0 <= k < a.Length && a[k] == res[i] &&
      forall k2 :: 0 <= k2 < k ==> a[k2] != res[i])
  ensures forall i, j :: 0 <= i < j < |res| ==>
      (exists k_i, k_j :: 0 <= k_i < k_j < a.Length && a[k_i] == res[i] && a[k_j] == res[j] &&
        forall k2 :: 0 <= k2 < k_i ==> a[k2] != res[i] &&
        forall k2 :: 0 <= k2 < k_j ==> a[k2] != res[j])
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall x: T :: x in res ==> x in b[..]
    invariant forall x: T :: x in res ==> x in a[..i]
    invariant forall x: T :: (x in a[..i] && x in b[..]) ==> x in res
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
    invariant forall t :: 0 <= t < |res| ==> (exists k :: 0 <= k < i && a[k] == res[t] &&
        forall k2 :: 0 <= k2 < k ==> a[k2] != res[t])
    invariant forall p, q :: 0 <= p < q < |res| ==>
        (exists k_p, k_q :: 0 <= k_p < k_q < i && a[k_p] == res[p] && a[k_q] == res[q] &&
          forall k2 :: 0 <= k2 < k_p ==> a[k2] != res[p] &&
          forall k2 :: 0 <= k2 < k_q ==> a[k2] != res[q])
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
