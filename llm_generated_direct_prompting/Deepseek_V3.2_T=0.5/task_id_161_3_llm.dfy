// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).
method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  requires a != null && b != null
  ensures |res| <= a.Length
  ensures forall i :: 0 <= i < |res| ==> res[i] in a[..]
  ensures forall i :: 0 <= i < |res| ==> res[i] !in b[..]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < |res| ==> res[i] !in a[..IndexInArray(a, res[i])]
  ensures forall x :: x in a[..] && x !in b[..] && x !in a[..FirstIndex(a, x)] ==> x in res
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant |res| <= i
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k :: 0 <= k < |res| ==> res[k] !in b[..]
    invariant forall k, l :: 0 <= k < l < |res| ==> res[k] != res[l]
    invariant forall k :: 0 <= k < |res| ==> res[k] !in a[..IndexInArray(a, res[k])]
    invariant forall x :: x in a[..i] && x !in b[..] && x !in a[..FirstIndexInPrefix(a, i, x)] ==> x in res
  {
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
}

ghost function IndexInArray<T(==)>(a: array<T>, x: T): int
  requires a != null
  requires x in a[..]
  ensures 0 <= IndexInArray(a, x) < a.Length
  ensures a[IndexInArray(a, x)] == x
  ensures forall k :: 0 <= k < IndexInArray(a, x) ==> a[k] != x
{
  if a[0] == x then 0 else 1 + IndexInArray(a[1..], x)
}

ghost function FirstIndex<T(==)>(a: array<T>, x: T): int
  requires a != null
  ensures 0 <= FirstIndex(a, x) <= a.Length
  ensures forall k :: 0 <= k < FirstIndex(a, x) ==> a[k] != x
  ensures FirstIndex(a, x) < a.Length ==> a[FirstIndex(a, x)] == x
{
  FirstIndexHelper(a, x, 0)
}

ghost function FirstIndexInPrefix<T(==)>(a: array<T>, n: int, x: T): int
  requires a != null
  requires 0 <= n <= a.Length
  ensures 0 <= FirstIndexInPrefix(a, n, x) <= n
  ensures forall k :: 0 <= k < FirstIndexInPrefix(a, n, x) ==> a[k] != x
  ensures FirstIndexInPrefix(a, n, x) < n ==> a[FirstIndexInPrefix(a, n, x)] == x
{
  FirstIndexHelper(a, x, 0, n)
}

ghost function FirstIndexHelper<T(==)>(a: array<T>, x: T, start: int, end: int): int
  requires a != null
  requires 0 <= start <= end <= a.Length
  ensures start <= FirstIndexHelper(a, x, start, end) <= end
  ensures forall k :: start <= k < FirstIndexHelper(a, x, start, end) ==> a[k] != x
  ensures FirstIndexHelper(a, x, start, end) < end ==> a[FirstIndexHelper(a, x, start, end)] == x
{
  if start == end then end
  else if a[start] == x then start
  else FirstIndexHelper(a, x, start+1, end)
}

// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);
  assert res1 == [1, 3];
}

  // Boundary cases
method RemoveElementsEmpty(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [];
  var res2 := RemoveElements(a1, a1);
  assert res2 == [];
  var res3 := RemoveElements(a1, a2);
  assert res3 == [1, 2, 3, 4];
}


// Duplicates in the first array
method RemoveElementsDups(){
  var a1 := new int[] [1, 2, 1, 3];
  var a3 := new int[] [1];
  var res1 := RemoveElements(a1, a3);
  assert res1 == [2, 3] ;
  var a2 := new int[] [1, 2, 1, 3, 2];
  var res2 := RemoveElements(a2, a3);
  assert res2 == [2, 3] ;
}

