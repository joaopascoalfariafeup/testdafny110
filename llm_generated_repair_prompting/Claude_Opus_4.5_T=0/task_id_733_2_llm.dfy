// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures index == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != target
    ensures index >= 0 ==> 0 <= index < arr.Length && arr[index] == target && forall k :: 0 <= k < index ==> arr[k] != target
{
    for i := 0 to arr.Length
        invariant forall k :: 0 <= k < i ==> arr[k] != target
    {
        if arr[i] == target {
            return i;
        }
        else if arr[i] > target {
            return -1;
        }
    }
    return -1;
}

// Test cases checked statically.
method FindFirstOccurrenceTest(){
    var a1 := new int[] [2, 5, 5, 5, 6, 6, 8, 9, 9, 9];
    
    // Helper assertions for the array contents
    assert a1[..] == [2, 5, 5, 5, 6, 6, 8, 9, 9, 9];
    assert a1[0] == 2;
    assert a1[1] == 5;
    
    var out1 := FindFirstOccurrence(a1, 5);
    // out1 >= 0 means a1[out1] == 5 and forall k < out1: a1[k] != 5
    // Since a1[0] == 2 != 5 and a1[1] == 5, out1 must be 1
    assert a1[0] != 5;
    assert a1[1] == 5;
    assert out1 == 1;

    assert a1[0] == 2 && a1[1] == 5 && a1[2] == 5 && a1[3] == 5;
    assert a1[4] == 6 && a1[5] == 6 && a1[6] == 8;
    assert a1[7] == 9 && a1[8] == 9 && a1[9] == 9;
    
    var out2 := FindFirstOccurrence(a1, 9);
    // Need to show that indices 0-6 don't have 9, and index 7 has 9
    assert a1[0] != 9 && a1[1] != 9 && a1[2] != 9 && a1[3] != 9;
    assert a1[4] != 9 && a1[5] != 9 && a1[6] != 9;
    assert a1[7] == 9;
    assert out2 == 7;

    var out3 := FindFirstOccurrence(a1, 1);
    // Need to show 1 is not in the array
    assert forall k :: 0 <= k < a1.Length ==> a1[k] != 1;
    assert out3 == -1;
}
