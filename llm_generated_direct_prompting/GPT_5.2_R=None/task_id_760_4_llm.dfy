// Checks if the given array has only one distinct element (or is empty).
method HasOnlyOneDistinctElement<T(==)>(a: array<T>) returns (result: bool)
    ensures result <==> (a.Length == 0 || (forall k :: 0 <= k < a.Length ==> a[k] == a[0]))
{
    if a.Length == 0 {
        return true;
    }
    var firstElement := a[0];
    for i := 1 to a.Length
        invariant 1 <= i <= a.Length
        invariant firstElement == a[0]
        invariant forall k :: 1 <= k < i ==> a[k] == firstElement
    {
        if a[i] != firstElement {
            return false;
        }
    }
    return true;
}

// Test cases checked statically.
method HasOnlyOneDistinctElementTest(){
    var a1 := new int[] [1, 1, 1];
    var res1 := HasOnlyOneDistinctElement(a1);
    assert res1;

    var a2 := new int[] [1, 2, 1, 2];
    var res2 := HasOnlyOneDistinctElement(a2);
    assert !res2;

    var a3 := new int[] [];
    var res3 := HasOnlyOneDistinctElement(a3);
    assert res3;
}

