// Ghost function to compute intersection preserving order from first array
ghost function seqIntersect<T(==)>(a: seq<T>, b: seq<T>): seq<T>
{
  if a == [] then []
  else if a[0] in b && a[0] !in seqIntersect(a[1..], b) then [a[0]] + seqIntersect(a[1..], b)
  else seqIntersect(a[1..], b)
}

// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in the first array.
// In case the first array has duplicates, it is kept an arbitrary occurrence.
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  ensures forall x :: x in res ==> x in a[..] && x in b[..]
  ensures forall x :: x in a[..] && x in b[..] ==> x in res
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[i]
{
  res := [];
  for i := 0 to a.Length
    invariant forall x :: x in res ==> x in a[..i] && x in b[..]
    invariant forall x :: x in a[..i] && x in b[..] ==> x in res
    invariant forall j, k :: 0 <= j < k < |res| ==> res[j] != res[k]
    invariant forall j :: 0 <= j < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[j]
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
  assert a[..] == [1, 2, 3];
  assert b[..] == [1, 3, 1];
  assert 1 in a[..] && 1 in b[..];
  assert 3 in a[..] && 3 in b[..];
  assert 2 in a[..] && 2 !in b[..];
  assert forall x :: x in res1 ==> x == 1 || x == 3;
  assert 1 in res1 && 3 in res1;
  assert |res1| >= 2;
  assert forall i, j :: 0 <= i < j < |res1| ==> res1[i] != res1[j];
  // Since res1 contains exactly 1 and 3, and they are distinct, |res1| == 2
  assert forall x :: x in res1 ==> x == 1 || x == 3;
  assert 1 in res1;
  assert 3 in res1;
  // Helper: if all elements are either 1 or 3, and both are present, and all distinct
  assert |res1| <= 2 by {
    if |res1| > 2 {
      assert res1[0] in res1 && res1[1] in res1 && res1[2] in res1;
      assert res1[0] == 1 || res1[0] == 3;
      assert res1[1] == 1 || res1[1] == 3;
      assert res1[2] == 1 || res1[2] == 3;
      assert res1[0] != res1[1] && res1[0] != res1[2] && res1[1] != res1[2];
      // This is impossible with only values 1 and 3
    }
  }
  assert |res1| == 2;
  assert (res1[0] == 1 && res1[1] == 3) || (res1[0] == 3 && res1[1] == 1);

  // Empty intersection
  var res2 := Intersection(b, c);
  assert b[..] == [1, 3, 1];
  assert c[..] == [2, 4, 6];
  assert 1 !in c[..] && 3 !in c[..];
  assert forall x :: x in b[..] ==> x !in c[..];
  assert forall x :: x in b[..] && x in c[..] ==> false;
  assert forall x :: x in res2 ==> x in b[..] && x in c[..];
  assert forall x :: x in res2 ==> false;
  assert |res2| == 0;
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert b[..] == [1, 3, 1];
  assert a[..] == [1, 2, 3];
  assert 1 in b[..] && 1 in a[..];
  assert 3 in b[..] && 3 in a[..];
  assert 1 in res3 && 3 in res3;
  assert forall x :: x in res3 ==> x in b[..] && x in a[..];
  assert forall x :: x in res3 ==> x == 1 || x == 3;
  assert |res3| <= 2 by {
    if |res3| > 2 {
      assert res3[0] != res3[1] && res3[0] != res3[2] && res3[1] != res3[2];
      assert res3[0] == 1 || res3[0] == 3;
      assert res3[1] == 1 || res3[1] == 3;
      assert res3[2] == 1 || res3[2] == 3;
    }
  }
  assert |res3| == 2;
  assert res3 == [1, 3] || res3 == [3, 1];
}
