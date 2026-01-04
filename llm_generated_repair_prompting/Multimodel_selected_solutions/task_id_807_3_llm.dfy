// Finds the index of the first odd number in an arrray.
// If there is no odd number, returns -1.
method FindFirstOdd(a: array<int>) returns (index: int)
    requires a != null
    ensures -1 <= index < a.Length
    ensures index == -1 ==> (forall k :: 0 <= k < a.Length ==> !IsOdd(a[k]))
    ensures index != -1 ==> IsOdd(a[index]) && (forall k :: 0 <= k < index ==> !IsOdd(a[k]))
{
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
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
    // Help Dafny use the concrete contents of the array
    assert a1[..] == [1, 3, 5];
    assert a1[0] == 1 && a1[1] == 3 && a1[2] == 5;
    assert IsOdd(a1[0]);

    var out1 := FindFirstOdd(a1);

    // Prove out1 == 0 from FindFirstOdd's postconditions and the concrete array
    if out1 == -1 {
        // contradicts IsOdd(a1[0]) and "no odds if -1"
        assert !IsOdd(a1[0]);
        assert false;
    } else {
        if out1 != 0 {
            assert 0 < out1;
            assert !IsOdd(a1[0]); // from forall k < out1
            assert false;
        }
    }
    assert out1 == 0;

    // last
    var a2 := new int[] [2, 4, 1];
    assert a2[..] == [2, 4, 1];
    assert a2[0] == 2 && a2[1] == 4 && a2[2] == 1;
    assert !IsOdd(a2[0]);
    assert !IsOdd(a2[1]);
    assert IsOdd(a2[2]);

    var out2 := FindFirstOdd(a2);

    // Prove out2 == 2
    if out2 == -1 {
        assert !IsOdd(a2[2]);
        assert false;
    } else {
        if out2 == 0 {
            assert IsOdd(a2[0]);
            assert false;
        }
        if out2 == 1 {
            // then k=0 < out2, so a2[0] must not be odd (ok), but also index 1 must be odd (contradiction)
            assert IsOdd(a2[1]);
            assert false;
        }
        // Only remaining possibility within bounds is 2
        assert out2 == 2;
    }
    assert out2 == 2;

    // none
    var a3 := new int[] [2, 6, 4];
    assert a3[..] == [2, 6, 4];

    var out3 := FindFirstOdd(a3);
    assert out3 == -1;
}
