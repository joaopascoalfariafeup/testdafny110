// Finds the index of the first odd number in an array.
// If there is no odd number, returns -1.
method FindFirstOdd(a: array<int>) returns (index: int)
  ensures 0 <= index < a.Length ==> IsOdd(a[index])
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> !IsOdd(a[k])
  ensures index != -1 ==> forall k :: 0 <= k < index ==> !IsOdd(a[k])
  ensures 0 <= index <= a.Length
  ensures index == -1 || (0 <= index < a.Length && IsOdd(a[index]))
{
    index := -1;
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant index == -1 || (0 <= index < i && IsOdd(a[index]))
        invariant index == -1 ==> forall k :: 0 <= k < i ==> !IsOdd(a[k])
    {
        if i < a.Length && IsOdd(a[i]) {
            index := i;
            break;
        }
    }
}

predicate IsOdd(x: int) {
    x % 2 != 0
}

// Test cases checked statically.
method FindFirstOddTest(){
    // first
    var a1 := new int[] [1, 3, 5];
    assert a1[..] == [1, 3, 5]; // helper
    var out1 := FindFirstOdd(a1);
    assert out1 == 0;

    // last
    var a2 := new int[] [2, 4, 1];
    assert a2[..] == [2, 4, 1]; // helper
    var out2 := FindFirstOdd(a2);
    assert out2 == 2;

    // none
    var a3 := new int[] [2, 6, 4];
    assert a3[..] == [2, 6, 4]; // helper
    var out3 := FindFirstOdd(a3);
    assert out3 == -1;
}

