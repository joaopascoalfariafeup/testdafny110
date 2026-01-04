// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).

// Helper function to find the first index of an element in an array
function FirstIndexInA<T(==)>(a: array<T>, x: T): int
  requires a != null
  ensures 0 <= FirstIndexInA(a, x) <= a.Length
  ensures FirstIndexInA(a, x) < a.Length ==> a[FirstIndexInA(a, x)] == x
  ensures forall k :: 0 <= k < FirstIndexInA(a, x) ==> a[k] != x
{
  FirstIndexInAHelper(a, x, 0)
}

function FirstIndexInAHelper<T(==)>(a: array<T>, x: T, start: int): int
  requires a != null && 0 <= start <= a.Length
  ensures start <= FirstIndexInAHelper(a, x, start) <= a.Length
  ensures FirstIndexInAHelper(a, x, start) < a.Length ==> a[FirstIndexInAHelper(a, x, start)] == x
  ensures forall k :: start <= k < FirstIndexInAHelper(a, x, start) ==> a[k] != x
{
  if start == a.Length then a.Length
  else if a[start] == x then start
  else FirstIndexInAHelper(a, x, start+1)
}

method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  requires a != null && b != null
  ensures |res| <= a.Length
  ensures forall i :: 0 <= i < |res| ==> res[i] in a[..]
  ensures forall i :: 0 <= i < |res| ==> res[i] !in b[..]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < |res| ==> res[i] !in a[..FirstIndexInA(a, res[i])]
  ensures forall k :: 0 <= k < a.Length && a[k] !in b[..] && a[k] !in a[..k] ==> a[k] in res
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant |res| <= i
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k :: 0 <= k < |res| ==> res[k] !in b[..]
    invariant forall k, l :: 0 <= k < l < |res| ==> res[k] != res[l]
    invariant forall k :: 0 <= k < |res| ==> res[k] !in a[..FirstIndexInA(a, res[k])]
    invariant forall x :: x in a[..i] && x !in b[..] && x !in a[..FirstIndexInA(a, x)] ==> x in res
  {
    if a[i] !in b[..] && a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
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
  var a2 := new int[] [1, 2, 1, 3, 2];
  var a3 := new int[] [1];
  var res1 := RemoveElements(a1, a3);
  assert res1 == [2, 3] ;
  var res2 := RemoveElements(a2, a3);
  assert res2 == [2, 3] ;
}


