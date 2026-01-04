// Checks if the given array has only one distinct element (or is empty).
method HasOnlyOneDistinctElement<T(==)>(a: array?<T>) returns (result: bool)
    requires a != null
    ensures result <==> (a.Length == 0 || (forall i :: 0 <= i < a.Length ==> a[i] == a[0]))
{
    if a.Length == 0 {
        return true;
    }
    var firstElement := a[0];

    if a.Length == 1 {
        // With length 1, the only index is 0, so the property holds trivially.
        assert forall i :: 0 <= i < a.Length ==> a[i] == a[0] by
        {
            forall i | 0 <= i < a.Length
                ensures a[i] == a[0]
            {
                assert i == 0;
            }
        }
        return true;
    }

    for i := 1 to a.Length - 1
        invariant 1 <= i <= a.Length
        invariant firstElement == a[0]
        invariant forall j :: 0 <= j < i ==> a[j] == firstElement
    {
        if a[i] != firstElement {
            assert 0 <= i < a.Length;
            assert a[i] != a[0];
            assert !(forall k :: 0 <= k < a.Length ==> a[k] == a[0]) by
            {
                // Provide a counterexample index i
                assert (forall k :: 0 <= k < a.Length ==> a[k] == a[0]) ==> a[i] == a[0];
            }
            return false;
        }
    }

    // At loop exit we have i == a.Length, so the invariant gives the full range.
    assert forall j :: 0 <= j < a.Length ==> a[j] == firstElement by
    {
        forall j | 0 <= j < a.Length
            ensures a[j] == firstElement
        {
            // Instantiate the loop invariant: since i == a.Length at loop exit, j < a.Length implies j < i
            assert j < a.Length;
            assert a[j] == firstElement;
        }
    }
    return true;
}

// Test cases checked statically.
method HasOnlyOneDistinctElementTest(){
    var a1 := new int[] [1, 1, 1];
    assert a1[..] == [1,1,1];
    var res1 := HasOnlyOneDistinctElement(a1);
    assert res1;

    var a2 := new int[] [1, 2, 1, 2];
    assert a2[..] == [1,2,1,2];
    var res2 := HasOnlyOneDistinctElement(a2);
    // Help the verifier with a concrete counterexample (index 1)
    assert a2.Length > 1;
    assert a2[1] != a2[0];
    assert !res2;

    var a3 := new int[] [];
    assert a3[..] == [];
    var res3 := HasOnlyOneDistinctElement(a3);
    assert res3;
}
