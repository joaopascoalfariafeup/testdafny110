// Takes two arrays and returns the set of elements that are in one array 
// but not in the other.
// Implemented using array and set operations.
method DissimilarElements<T(==)>(a: array<T>, b: array<T>) returns (res: set<T>)
  ensures res == (set i | 0 <= i < a.Length :: a[i]) - (set i | 0 <= i < b.Length :: b[i]) + (set i | 0 <= i < b.Length :: b[i]) - (set i | 0 <= i < a.Length :: a[i])
{
    var only_in_a : set<T> := {};
    for i := 0 to a.Length
      invariant only_in_a == (set j | 0 <= j < i :: a[j]) - (set k | 0 <= k < b.Length :: b[k])
    {
        var c := contains(b, a[i]);
        if !c {
            only_in_a := only_in_a + {a[i]};
        }
    }

    var only_in_b : set<T> := {};
    for i := 0 to b.Length
      invariant only_in_b == (set j | 0 <= j < i :: b[j]) - (set k | 0 <= k < a.Length :: a[k])
    {
        var c := contains(a, b[i]);
        if !c {
            only_in_b  := only_in_b  + {b[i]};
        }
    }

    // Prove the final postcondition
    // only_in_a = A - B where A = set of a, B = set of b
    // only_in_b = B - A
    // So only_in_a + only_in_b = (A - B) ∪ (B - A) = symmetric difference
    // The postcondition is: (A - B) ∪ (B - A)
    // We need to show that (A - B) ∪ (B - A) = (A - B) + (B - A) (set union)
    // and that this equals the expression in the postcondition
    // The postcondition expression is: (A - B) + (B - A) (same as what we have)
    // So we just need to show that our only_in_a and only_in_b satisfy this
    // which they do by the loop invariants
    // Add an assertion to help Dafny connect the dots
    assert only_in_a == (set i | 0 <= i < a.Length :: a[i]) - (set i | 0 <= i < b.Length :: b[i]);
    assert only_in_b == (set i | 0 <= i < b.Length :: b[i]) - (set i | 0 <= i < a.Length :: a[i]);
    return only_in_a  + only_in_b;
}

// Checks if an element x is in an array a, using only array operations.
method contains<T(==)>(a: array<T>, x: T) returns (res: bool)
  ensures res <==> (exists i | 0 <= i < a.Length :: a[i] == x)
{
    res := false;
    for i := 0 to a.Length
      invariant !res ==> (forall j | 0 <= j < i :: a[j] != x)
      invariant res <==> (exists j | 0 <= j < i :: a[j] == x)
    {
        if a[i] == x {
            res := true;
            break;
        }
    }
}


// Test cases checked statically by Dafny.
method DissimilarElementsTest(){
    var a1 := new int[] [3, 4, 3, 5, 6];
    var a2 := new int[] [5, 7, 4, 10, 5];
    var res1 := DissimilarElements(a1, a2);
    // Add helper assertions to prove the test assertion
    assert (set i | 0 <= i < a1.Length :: a1[i]) == {3, 4, 5, 6};
    assert (set i | 0 <= i < a2.Length :: a2[i]) == {4, 5, 7, 10};
    assert ({3, 4, 5, 6} - {4, 5, 7, 10}) == {3, 6};
    assert ({4, 5, 7, 10} - {3, 4, 5, 6}) == {7, 10};
    assert {3, 6} + {7, 10} == {3, 6, 7, 10};
    assert res1 == {3, 6, 7, 10};

    var res2 := DissimilarElements(a1, a1);
    assert (set i | 0 <= i < a1.Length :: a1[i]) == {3, 4, 5, 6};
    assert ({3, 4, 5, 6} - {3, 4, 5, 6}) == {};
    assert {} as set<int> + ({} as set<int>) == {};
    assert res2 == {};

    var a3 := new int[] [];
    var res3 := DissimilarElements(a1, a3);
    assert (set i | 0 <= i < a3.Length :: a3[i]) == {};
    assert ({3, 4, 5, 6} - {}) == {3, 4, 5, 6};
    assert {} - {3, 4, 5, 6} == {};
    assert {3, 4, 5, 6} + {} == {3, 4, 5, 6};
    assert  res3 == {3, 4, 5, 6};
}


