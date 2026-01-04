
// Checks if the given array has only one distinct element (or is empty).
method HasOnlyOneDistinctElement<T(==)>(a: array<T>) returns (result: bool)
  ensures result == (forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j])
  ensures result == (a.Length == 0 || (forall k :: 0 <= k < a.Length ==> a[k] == a[0]))
  ensures !result ==> (exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j])
  // Add a more specific postcondition to help with verification
  ensures !result ==> (exists i :: 1 <= i < a.Length && a[i] != a[0])
{
    if a.Length == 0 {
        return true;
    }
    var firstElement := a[0];
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> a[k] == firstElement
    {
        if a[i] != firstElement {
            // We found a counterexample: a[i] != a[0]
            // This directly proves the new postcondition
            return false;
        }
    }
    return true;
}

// Test cases checked statically.
method HasOnlyOneDistinctElementTest(){
    var a1 := new int[] [1, 1, 1];
    // Helper assertion to help Dafny know array contents
    assert a1[..] == [1, 1, 1];
    var res1 := HasOnlyOneDistinctElement(a1);
    assert res1;

    var a2 := new int[] [1, 2, 1, 2];
    // Helper assertion to help Dafny know array contents  
    assert a2[..] == [1, 2, 1, 2];
    // Additional helper assertions to help Dafny see there are different elements
    assert a2[0] == 1;
    assert a2[1] == 2;
    assert a2[0] != a2[1];
    var res2 := HasOnlyOneDistinctElement(a2);
    // Now Dafny should be able to prove this using the new postcondition
    // The new postcondition says: !res2 ==> (exists i :: 1 <= i < a2.Length && a2[i] != a2[0])
    // We know a2[1] = 2 and a2[0] = 1, so a2[1] != a2[0]
    // Therefore !res2 must be true
    assert !res2;

    var a3 := new int[] [];
    var res3 := HasOnlyOneDistinctElement(a3);
    assert res3;
}
