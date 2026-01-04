// Determines the last position of an element 'elem' in a sorted array 'arr'.
// If the element is not in the array, the method returns -1.
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != elem
    ensures pos >= 0 ==> 0 <= pos < arr.Length && arr[pos] == elem
    ensures pos >= 0 ==> forall k :: pos < k < arr.Length ==> arr[k] > elem
    ensures (exists k :: 0 <= k < arr.Length && arr[k] == elem) ==> pos >= 0
{
    // Scan from the end of the array to the begin of the array.
    var i := arr.Length - 1;
    while i >= 0 && arr[i] > elem
        invariant -1 <= i < arr.Length
        invariant forall k :: i < k < arr.Length ==> arr[k] > elem
    {        
        i := i - 1;
    }
    if i >= 0 && arr[i] == elem {
        return i;
    }
    return -1;
}

// Test cases checked statically.
method LastPositionTest(){
    var a1 := new int[] [1, 1, 1, 2, 3, 4, 4];
    assert a1[..] == [1, 1, 1, 2, 3, 4, 4];

    var out1 := LastPosition(a1, 1);
    assert a1[0] == 1 && a1[1] == 1 && a1[2] == 1 && a1[3] == 2;
    assert a1[3] > 1 && a1[4] > 1 && a1[5] > 1 && a1[6] > 1;
    assert exists k :: 0 <= k < a1.Length && a1[k] == 1;
    assert out1 >= 0 && a1[out1] == 1;
    assert forall k :: out1 < k < a1.Length ==> a1[k] > 1;
    assert out1 == 2;

    var out2 := LastPosition(a1, 4);
    assert a1[6] == 4;
    assert exists k :: 0 <= k < a1.Length && a1[k] == 4;
    assert out2 >= 0 && a1[out2] == 4;
    assert out2 == 6;

    var out3 := LastPosition(a1, 5);
    assert forall k :: 0 <= k < a1.Length ==> a1[k] != 5;
    assert out3 == -1;

    var out4 := LastPosition(a1, 0);
    assert a1[0] == 1 > 0;
    assert forall k :: 0 <= k < a1.Length ==> a1[k] != 0;
    assert out4 == -1;
}
