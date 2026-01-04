// Checks if the given array has only one distinct element (or is empty).
method HasOnlyOneDistinctElement<T(==)>(a: array<T>) returns (result: bool)
    ensures result <==> (a.Length == 0 || forall i :: 0 <= i < a.Length ==> a[i] == a[0])
{
    if a.Length == 0 {
        return true;
    }
    var firstElement := a[0];
    for i := 1 to a.Length
        invariant forall k :: 0 <= k < i ==> a[k] == firstElement
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
    assert a2[..] == [1, 2, 1, 2];
    assert a2[0] == 1;
    assert a2[1] == 2;
    assert a2[1] != a2[0];
    var res2 := HasOnlyOneDistinctElement(a2);
    assert exists i :: 0 <= i < a2.Length && a2[i] != a2[0];
    assert !res2;

    var a3 := new int[] [];
    var res3 := HasOnlyOneDistinctElement(a3);
    assert res3;
}
