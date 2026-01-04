// Finds the index of the first odd number in an arrray.
// If there is no odd number, returns -1.
method FindFirstOdd(a: array<int>) returns (index: int)
    ensures -1 <= index < a.Length
    ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> !IsOdd(a[k])
    ensures index >= 0 ==> IsOdd(a[index])
    ensures index >= 0 ==> forall k :: 0 <= k < index ==> !IsOdd(a[k])
    ensures (exists k :: 0 <= k < a.Length && IsOdd(a[k])) ==> index >= 0
{
    for i := 0 to a.Length
        invariant forall k :: 0 <= k < i ==> !IsOdd(a[k])
    {
        if IsOdd(a[i]) {
            return i;
        }
    }
    return -1;
}


predicate IsOdd(x: int) {
    x % 2 != 0
}

// Test cases checked statically.
method FindFirstOddTest(){
    // first
    var a1 := new int[] [1, 3, 5];
    assert a1[0] == 1 && a1[1] == 3 && a1[2] == 5;
    assert IsOdd(a1[0]);
    // Provide explicit witness for the existential
    assert 0 <= 0 < a1.Length && IsOdd(a1[0]);
    assert exists k :: 0 <= k < a1.Length && IsOdd(a1[k]);

    var out1 := FindFirstOdd(a1);
    // Since IsOdd(a1[0]) and postcondition says all before index are not odd,
    // index must be 0
    assert out1 >= 0;
    assert IsOdd(a1[out1]);
    assert forall k :: 0 <= k < out1 ==> !IsOdd(a1[k]);
    // If out1 > 0, then !IsOdd(a1[0]), but we know IsOdd(a1[0]), contradiction
    assert out1 == 0;

    // last
    var a2 := new int[] [2, 4, 1];
    assert a2[0] == 2 && a2[1] == 4 && a2[2] == 1;
    assert !IsOdd(a2[0]) && !IsOdd(a2[1]) && IsOdd(a2[2]);
    // Provide explicit witness for the existential
    assert 0 <= 2 < a2.Length && IsOdd(a2[2]);
    assert exists k :: 0 <= k < a2.Length && IsOdd(a2[k]);

    var out2 := FindFirstOdd(a2);
    assert out2 >= 0;
    assert IsOdd(a2[out2]);
    assert forall k :: 0 <= k < out2 ==> !IsOdd(a2[k]);
    // out2 can't be 0 or 1 since a2[0] and a2[1] are not odd
    // out2 must be 2 since a2[2] is odd
    assert out2 == 2;

    // none
    var a3 := new int[] [2, 6, 4];
    assert a3[0] == 2 && a3[1] == 6 && a3[2] == 4;
    assert !IsOdd(a3[0]) && !IsOdd(a3[1]) && !IsOdd(a3[2]);
    
    var out3 := FindFirstOdd(a3);
    assert out3 == -1;
}

