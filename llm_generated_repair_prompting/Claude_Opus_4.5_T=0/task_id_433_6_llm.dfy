// Checks if a number 'n' is greater than all elements in an array 'a'
method IsGreater(n: int, a: array<int>) returns (result: bool)
    ensures result <==> forall k :: 0 <= k < a.Length ==> n > a[k]
{
    for i := 0 to a.Length
        invariant forall k :: 0 <= k < i ==> n > a[k]
    {
        if n <= a[i] {
            return false;
        }
    }
    return true;
}

// Test cases checked statically
method IsGreaterTest(){
    var a1 := new int[] [3, 2, 1, 5, 2];
    assert a1[..] == [3, 2, 1, 5, 2]; // helper
    assert a1[3] == 5; // helper: 4 is not greater than 5
    assert !(4 > a1[3]); // helper: 4 is not greater than a1[3]
    assert 0 <= 3 < a1.Length && !(4 > a1[3]); // helper: witness for exists
    assert exists k :: 0 <= k < a1.Length && !(4 > a1[k]); // helper: explicit exists
    assert !(forall k :: 0 <= k < a1.Length ==> 4 > a1[k]); // helper: negation of postcondition condition
    var out1 := IsGreater(4, a1);
    assert a1[..] == [3, 2, 1, 5, 2]; // helper: array unchanged
    assert a1[3] == 5; // helper
    assert !(4 > a1[3]); // helper
    assert !(forall k :: 0 <= k < a1.Length ==> 4 > a1[k]); // helper after call
    assert ! out1;

    var out2 := IsGreater(6, a1);
    assert out2;
}

