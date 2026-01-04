
// Checks if the given array has only one distinct element (or is empty).
method HasOnlyOneDistinctElement<T(==)>(a: array<T>) returns (result: bool)
    ensures result ==> (forall k :: 0 <= k < a.Length ==> a[k] == a[0])
    ensures !result ==> (exists k, l :: 0 <= k < a.Length && 0 <= l < a.Length && k != l && a[k] != a[l]) &&
                        (forall k, l :: 0 <= k < a.Length && 0 <= l < a.Length && k != l ==> a[k] != a[l])
{
    if a.Length == 0 {
        return true;
    }
    var firstElement := a[0];
    for i := 1 to a.Length
        invariant forall k :: 0 <= k < i ==> a[k] == firstElement
        invariant exists k :: 0 <= k < i ==> a[k] == firstElement
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
    assert a1[..] == [1, 1, 1]; // helper
    var res1 := HasOnlyOneDistinctElement(a1);
    assert res1;

    var a2 := new int[] [1, 2, 1, 2];
    assert a2[..] == [1, 2, 1, 2]; // helper
    var res2 := HasOnlyOneDistinctElement(a2);
    assert !res2;

    var a3 := new int[] [];
    assert a3[..] == []; // helper
    var res3 := HasOnlyOneDistinctElement(a3);
    assert res3;
}

