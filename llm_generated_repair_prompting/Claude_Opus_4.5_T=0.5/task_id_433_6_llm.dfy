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
    assert a1[..] == [3, 2, 1, 5, 2]; // helper assertion
    assert a1[0] == 3 && a1[1] == 2 && a1[2] == 1 && a1[3] == 5 && a1[4] == 2; // helper
    assert a1.Length == 5; // helper
    assert 0 <= 3 < a1.Length; // helper: index 3 is valid
    assert a1[3] == 5; // helper: element at index 3 is 5
    assert 4 <= a1[3]; // helper: 4 is not greater than 5
    var out1 := IsGreater(4, a1);
    assert ! out1;

    var out2 := IsGreater(6, a1);
    assert out2;
}
