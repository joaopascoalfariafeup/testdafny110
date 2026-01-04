// Returns a sequence with all elements belonging to the first array 
// that are not in the second array, by the same order, without duplicates
// (keeping only the first occurrence).

// Helper function to find the first index of an element in an array
function FirstIndexInA<T(==)>(a: array<T>, x: T): int
  reads a
  requires a != null
  ensures 0 <= FirstIndexInA(a, x) <= a.Length
  ensures FirstIndexInA(a, x) < a.Length ==> a[FirstIndexInA(a, x)] == x
  ensures forall k :: 0 <= k < FirstIndexInA(a, x) ==> a[k] != x
  decreases a.Length - FirstIndexInAHelper(a, x, 0)
{
  FirstIndexInAHelper(a, x, 0)
}

function FirstIndexInAHelper<T(==)>(a: array<T>, x: T, start: int): int
  reads a
  requires a != null && 0 <= start <= a.Length
  ensures start <= FirstIndexInAHelper(a, x, start) <= a.Length
  ensures FirstIndexInAHelper(a, x, start) < a.Length ==> a[FirstIndexInAHelper(a, x, start)] == x
  ensures forall k :: start <= k < FirstIndexInAHelper(a, x, start) ==> a[k] != x
  decreases a.Length - start
{
  if start == a.Length then a.Length
  else if a[start] == x then start
  else FirstIndexInAHelper(a, x, start+1)
}

// Helper predicate to define ordering preservation
ghost predicate OrderingPreserved<T(==)>(a: array<T>, res: seq<T>) 
  requires a != null
  reads a
{
  forall i :: 0 <= i < |res| ==> 
    FirstIndexInA(a, res[i]) < a.Length &&
    (forall j :: 0 <= j < i ==> FirstIndexInA(a, res[j]) < FirstIndexInA(a, res[i]))
}

// Helper lemma to prove ordering preservation when adding a new element
lemma {:induction false} OrderingPreservedAdd<T(==)>(a: array<T>, res: seq<T>, x: T)
  requires a != null
  requires forall i :: 0 <= i < |res| ==> FirstIndexInA(a, res[i]) < a.Length
  requires forall i, j :: 0 <= i < j < |res| ==> FirstIndexInA(a, res[i]) < FirstIndexInA(a, res[j])
  requires FirstIndexInA(a, x) < a.Length
  requires forall i :: 0 <= i < |res| ==> FirstIndexInA(a, res[i]) < FirstIndexInA(a, x)
  ensures OrderingPreserved(a, res + [x])
{
  // The lemma body is empty; the postcondition follows from the preconditions
}

method RemoveElements<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  requires a != null && b != null
  ensures |res| <= a.Length
  ensures forall i :: 0 <= i < |res| ==> res[i] in a[..]
  ensures forall i :: 0 <= i < |res| ==> res[i] !in b[..]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < |res| ==> FirstIndexInA(a, res[i]) < a.Length && res[i] !in a[..FirstIndexInA(a, res[i])]
  ensures forall k :: 0 <= k < a.Length && a[k] !in b[..] && a[k] !in a[..k] ==> a[k] in res
  ensures OrderingPreserved(a, res)
{
  res := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant |res| <= i
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall k :: 0 <= k < |res| ==> res[k] !in b[..]
    invariant forall k, l :: 0 <= k < l < |res| ==> res[k] != res[l]
    invariant forall k :: 0 <= k < |res| ==> FirstIndexInA(a, res[k]) < a.Length && res[k] !in a[..FirstIndexInA(a, res[k])]
    invariant forall x :: x in a[..i] && x !in b[..] && x !in a[..FirstIndexInA(a, x)] ==> x in res
    invariant OrderingPreserved(a, res)
    invariant forall k, l :: 0 <= k < l < |res| ==> FirstIndexInA(a, res[k]) < FirstIndexInA(a, res[l])
  {
    if a[i] !in b[..] && a[i] !in a[..i] {
      // Prove ordering preservation
      assert forall j :: 0 <= j < |res| ==> FirstIndexInA(a, res[j]) < i;
      assert FirstIndexInA(a, a[i]) == i;
      // Use lemma to maintain ordering invariant
      OrderingPreservedAdd(a, res, a[i]);
      res := res + [a[i]];
    }
    i := i + 1;
  }
}

// Test cases checked statically
method RemoveElementsTest(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [2, 4];
  var res1 := RemoveElements(a1, a2);
  // Helper assertions
  assert a1[..] == [1, 2, 3, 4];
  assert a2[..] == [2, 4];
  // Additional helper assertions to prove the result
  assert a1[0] == 1 && a1[1] == 2 && a1[2] == 3 && a1[3] == 4;
  assert 1 !in a2[..];
  assert 2 in a2[..];
  assert 3 !in a2[..];
  assert 4 in a2[..];
  assert 1 !in a1[..0];
  assert 3 !in a1[..2];
  // Prove the result using the postconditions
  assert |res1| == 2;
  assert res1[0] == 1;
  assert res1[1] == 3;
  assert res1 == [1, 3];
}

// Boundary cases
method RemoveElementsEmpty(){
  var a1 := new int[] [1, 2, 3, 4];
  var a2 := new int[] [];
  var res2 := RemoveElements(a1, a1);
  // Helper assertions
  assert a1[..] == [1, 2, 3, 4];
  // All elements of a1 are in b[..] (since b = a1)
  assert 1 in a1[..];
  assert 2 in a1[..];
  assert 3 in a1[..];
  assert 4 in a1[..];
  // Prove res2 is empty using postconditions
  assert |res2| == 0;
  assert res2 == [];
  var res3 := RemoveElements(a1, a2);
  // All elements of a1 are not in b[..] (since b is empty)
  assert 1 !in a2[..];
  assert 2 !in a2[..];
  assert 3 !in a2[..];
  assert 4 !in a2[..];
  // Check first occurrence condition
  assert 1 !in a1[..0];
  assert 2 !in a1[..1];
  assert 3 !in a1[..2];
  assert 4 !in a1[..3];
  // Prove the result using postconditions
  assert |res3| == 4;
  assert res3[0] == 1;
  assert res3[1] == 2;
  assert res3[2] == 3;
  assert res3[3] == 4;
  assert res3 == [1, 2, 3, 4];
}

// Duplicates in the first array
method RemoveElementsDups(){
  var a1 := new int[] [1, 2, 1, 3];
  var a3 := new int[] [1];
  var res1 := RemoveElements(a1, a3);
  // Helper assertions
  assert a1[..] == [1, 2, 1, 3];
  assert a3[..] == [1];
  // Check conditions for each element
  assert a1[0] == 1 && 1 in a3[..];  // Should not be included
  assert a1[1] == 2 && 2 !in a3[..] && 2 !in a1[..1];  // Should be included
  assert a1[2] == 1 && 1 in a3[..];  // Should not be included
  assert a1[3] == 3 && 3 !in a3[..] && 3 !in a1[..3];  // Should be included
  // Prove the result using postconditions
  assert |res1| == 2;
  assert res1[0] == 2;
  assert res1[1] == 3;
  assert res1 == [2, 3];
  
  var a2 := new int[] [1, 2, 1, 3, 2];
  var res2 := RemoveElements(a2, a3);
  assert a2[..] == [1, 2, 1, 3, 2];
  // Check conditions for each element
  assert a2[0] == 1 && 1 in a3[..];  // Should not be included
  assert a2[1] == 2 && 2 !in a3[..] && 2 !in a2[..1];  // Should be included
  assert a2[2] == 1 && 1 in a3[..];  // Should not be included
  assert a2[3] == 3 && 3 !in a3[..] && 3 !in a2[..3];  // Should be included
  assert a2[4] == 2 && 2 !in a3[..] && 2 in a2[..4];  // Should not be included (duplicate)
  // Prove the result using postconditions
  assert |res2| == 2;
  assert res2[0] == 2;
  assert res2[1] == 3;
  assert res2 == [2, 3];
}


