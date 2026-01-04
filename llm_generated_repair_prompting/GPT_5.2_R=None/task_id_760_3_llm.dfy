// Checks if the given array has only one distinct element (or is empty).
method HasOnlyOneDistinctElement<T(==)>(a: array?<T>) returns (result: bool)
    requires a != null
    ensures result <==> (a.Length == 0 || (forall i :: 0 <= i < a.Length ==> a[i] == a[0]))
{
    if a.Length == 0 {
        return true;
    }
    var firstElement := a[0];

    // If the array has length 1, the loop bounds 1..a.Length-1 would be invalid.
    if a.Length == 1 {
        return true;
    }

    for i := 1 to a.Length - 1
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] == firstElement
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
