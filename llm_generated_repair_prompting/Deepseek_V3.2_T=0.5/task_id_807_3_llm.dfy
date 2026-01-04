// Finds the index of the first odd number in an arrray.
// If there is no odd number, returns -1.
method FindFirstOdd(a: array<int>) returns (index: int)
  ensures 0 <= index < a.Length ==> IsOdd(a[index]) && (forall k :: 0 <= k < index ==> !IsOdd(a[k]))
  ensures index == -1 ==> (forall k :: 0 <= k < a.Length ==> !IsOdd(a[k]))
{
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> !IsOdd(a[k])
    {
        if IsOdd(a[i]) {
            index := i;
            return;
        }
        i := i + 1;
    }
    index := -1;
}


predicate IsOdd(x: int) {
    x % 2 != 0
}

// Test cases checked statically.
method FindFirstOddTest(){
    // first
    var a1 := new int[] [1, 3, 5];
    // Helper assertions to establish array contents
    assert a1[0] == 1 && a1[1] == 3 && a1[2] == 5;
    // Additional helper to prove IsOdd for array elements
    assert IsOdd(a1[0]);
    assert IsOdd(a1[1]);
    assert IsOdd(a1[2]);
    var out1 := FindFirstOdd(a1);
    assert out1 == 0;

    // last
    var a2 := new int[] [2, 4, 1];
    assert a2[0] == 2 && a2[1] == 4 && a2[2] == 1;
    assert !IsOdd(a2[0]);
    assert !IsOdd(a2[1]);
    assert IsOdd(a2[2]);
    var out2 := FindFirstOdd(a2);
    assert out2 == 2;

    // none
    var a3 := new int[] [2, 6, 4];
    assert a3[0] == 2 && a3[1] == 6 && a3[2] == 4;
    assert !IsOdd(a3[0]);
    assert !IsOdd(a3[1]);
    assert !IsOdd(a3[2]);
    var out3 := FindFirstOdd(a3);
    assert out3 == -1;
}


