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
    assert a1[0] == 3 && a1[1] == 2 && a1[2] == 1 && a1[3] == 5 && a1[4] == 2; // helper
    assert a1.Length == 5; // helper
    var out1 := IsGreater(4, a1);
    // Helper: show that 4 is not greater than a1[3] = 5
    assert a1[3] == 5;
    assert !(4 > a1[3]);
    // Therefore the forall is false
    assert !(forall k :: 0 <= k < a1.Length ==> 4 > a1[k]);
    assert ! out1;

    var out2 := IsGreater(6, a1);
    // Helper: show 6 is greater than all elements
    assert 6 > a1[0] && 6 > a1[1] && 6 > a1[2] && 6 > a1[3] && 6 > a1[4];
    assert forall k :: 0 <= k < a1.Length ==> 6 > a1[k];
    assert out2;
}
