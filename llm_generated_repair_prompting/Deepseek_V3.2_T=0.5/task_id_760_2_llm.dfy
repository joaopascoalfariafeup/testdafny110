// Checks if the given array has only one distinct element (or is empty).
method HasOnlyOneDistinctElement<T(==)>(a: array<T>) returns (result: bool)
  ensures result == (forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j])
  ensures result == (a.Length == 0 || (forall k :: 0 <= k < a.Length ==> a[k] == a[0]))
  ensures !result ==> (exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j])
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
            // Provide explicit witness for the existential in the postcondition
            // We have a[0] == firstElement and a[i] != firstElement
            // So a[0] != a[i]
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
    var res2 := HasOnlyOneDistinctElement(a2);
    assert !res2;

    var a3 := new int[] [];
    var res3 := HasOnlyOneDistinctElement(a3);
    assert res3;
}
