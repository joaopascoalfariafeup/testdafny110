// Takes two arrays and returns the set of elements that are in one array 
// but not in the other.
// Implemented using array and set operations.
method DissimilarElements<T(==)>(a: array<T>, b: array<T>) returns (res: set<T>)
    ensures res == (set x | x in a[..] && x !in b[..]) + (set x | x in b[..] && x !in a[..]) 
{
    var only_in_a : set<T> := {};
    for i := 0 to a.Length
        invariant only_in_a == (set x | x in a[..i] && x !in b[..])
    {
        var c := contains(b, a[i]);
        if !c {
            only_in_a := only_in_a + {a[i]};
        }
    }

    var only_in_b : set<T> := {};
    for i := 0 to b.Length
        invariant only_in_b  == (set x | x in b[..i] && x !in a[..])
    {
        var c := contains(a, b[i]);
        if !c {
            only_in_b  := only_in_b  + {b[i]};
        }
    }

    return only_in_a  + only_in_b;
}

// Checks if an element x is in an array a, using only array operations.
method contains<T(==)>(a: array<T>, x: T) returns (res: bool)
    ensures res <==> x in a[..]
{
    res := false;
    for i := 0 to a.Length
        invariant x !in a[0..i]
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
    assert a1[..] == [3, 4, 3, 5, 6]; // proof helper (array as seq)
    assert a2[..] == [5, 7, 4, 10, 5]; // proof helper (array as seq)
    assert res1 == {3, 6, 7, 10};

    var res2 := DissimilarElements(a1, a1);
    assert res2 == {};

    var a3 := new int[] [];
    var res3 := DissimilarElements(a1, a3);
    assert  res3 == {3, 4, 5, 6};
}