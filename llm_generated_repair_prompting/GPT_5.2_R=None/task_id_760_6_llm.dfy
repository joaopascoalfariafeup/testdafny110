// Checks if the given array has only one distinct element (or is empty).
method HasOnlyOneDistinctElement<T(==)>(a: array?<T>) returns (result: bool)
    requires a != null
    ensures result <==> (a.Length == 0 || (forall i :: 0 <= i < a.Length ==> a[i] == a[0]))
{
    if a.Length == 0 {
        // Postcondition simplifies to: result <==> true
        return true;
    }
    var firstElement := a[0];

    // If the array has length 1, the loop bounds 1..a.Length-1 would be invalid.
    if a.Length == 1 {
        // Prove: forall i :: 0 <= i < 1 ==> a[i] == a[0]
        assert forall i :: 0 <= i < a.Length ==> a[i] == a[0] by {
            // Only possible i is 0
            assert forall i :: 0 <= i < a.Length ==> i == 0;
        };
        return true;
    }

    for i := 1 to a.Length - 1
        invariant 1 <= i <= a.Length
        invariant firstElement == a[0]
        invariant forall j :: 0 <= j < i ==> a[j] == firstElement
    {
        if a[i] != firstElement {
            // Witness for the negation of the universal property in the postcondition
            assert 0 <= i < a.Length;
            assert a[i] != a[0];
            assert !(forall k :: 0 <= k < a.Length ==> a[k] == a[0]) by {
                // Instantiate the universal at k := i
                assert (forall k :: 0 <= k < a.Length ==> a[k] == a[0]) ==> a[i] == a[0];
            }
            return false;
        }
    }
    // At loop end, i == a.Length, so invariant gives the desired forall for the whole array
    assert forall j :: 0 <= j < a.Length ==> a[j] == firstElement;
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
