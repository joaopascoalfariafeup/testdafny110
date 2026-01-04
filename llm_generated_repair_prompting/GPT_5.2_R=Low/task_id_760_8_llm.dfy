// Proof helper: a single mismatch implies not all elements equal to a[0]
lemma MismatchImpliesNotAllEqual<T>(a: array<T>, j: int)
  requires a.Length > 0
  requires 0 <= j < a.Length
  requires a[j] != a[0]
  ensures !(forall i :: 0 <= i < a.Length ==> a[i] == a[0])
{
  if (forall i :: 0 <= i < a.Length ==> a[i] == a[0]) {
    assert a[j] == a[0];
    assert false;
  }
}

// Checks if the given array has only one distinct element (or is empty).
method HasOnlyOneDistinctElement<T(==)>(a: array<T>) returns (result: bool)
    modifies {}
    ensures result <==> (a.Length == 0 || (forall i :: 0 <= i < a.Length ==> a[i] == a[0]))
{
    if a.Length == 0 {
        return true;
    }
    var firstElement := a[0];
    for i := 1 to a.Length
        invariant 1 <= i <= a.Length
        invariant firstElement == a[0]
        invariant forall j :: 1 <= j < i ==> a[j] == firstElement
    {
        assert 0 <= i < a.Length;

        if a[i] != firstElement {
            assert a.Length > 0;
            assert a[i] != a[0];
            MismatchImpliesNotAllEqual(a, i);
            return false;
        }
    }
    // At this point, i == a.Length, so all indices 1..a.Length-1 match a[0]
    assert forall k :: 0 <= k < a.Length ==> a[k] == a[0];
    return true;
}

// Test cases checked statically.
method HasOnlyOneDistinctElementTest(){
    var a1 := new int[] [1, 1, 1];
    assert a1[..] == [1, 1, 1];
    var res1 := HasOnlyOneDistinctElement(a1);
    assert res1;

    var a2 := new int[] [1, 2, 1, 2];
    assert a2[..] == [1, 2, 1, 2];
    assert 0 <= 1 < a2.Length;
    assert a2.Length > 0;
    assert a2[1] != a2[0];
    MismatchImpliesNotAllEqual(a2, 1);
    assert !(forall i :: 0 <= i < a2.Length ==> a2[i] == a2[0]);
    assert a2.Length != 0;
    assert !(a2.Length == 0 || (forall i :: 0 <= i < a2.Length ==> a2[i] == a2[0]));

    var res2 := HasOnlyOneDistinctElement(a2);

    // Use the postcondition equivalence plus the already-proved mismatch fact
    assert res2 <==> (a2.Length == 0 || (forall i :: 0 <= i < a2.Length ==> a2[i] == a2[0]));
    assert a2[1] != a2[0]; // re-trigger the mismatch fact after the call
    MismatchImpliesNotAllEqual(a2, 1);
    assert !(a2.Length == 0 || (forall i :: 0 <= i < a2.Length ==> a2[i] == a2[0]));
    assert !res2;

    var a3 := new int[] [];
    assert a3[..] == [];
    var res3 := HasOnlyOneDistinctElement(a3);
    assert res3;
}
