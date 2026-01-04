// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures index == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != target
    ensures index >= 0 ==> 0 <= index < arr.Length && arr[index] == target && forall k :: 0 <= k < index ==> arr[k] != target
    ensures
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
    
    // Helper assertions for out1
    assert a1[0] == 2;
    assert a1[1] == 5;
    assert a1[0] != 5;
    
    var out1 := FindFirstOccurrence(a1, 5);
    // From postcondition: a1[out1] == 5 and forall k :: 0 <= k < out1 ==> a1[k] != 5
    // Since a1[0] != 5 and a1[1] == 5, out1 must be 1
    assert out1 == 1;

    // Helper assertions for out2
    assert a1[0] == 2 && a1[1] == 5 && a1[2] == 5 && a1[3] == 5;
    assert a1[4] == 6 && a1[5] == 6 && a1[6] == 8;
    assert a1[7] == 9;
    assert a1[0] != 9 && a1[1] != 9 && a1[2] != 9 && a1[3] != 9;
    assert a1[4] != 9 && a1[5] != 9 && a1[6] != 9;
    
    var out2 := FindFirstOccurrence(a1, 9);
    assert out2 == 7;

    // Helper assertions for out3
    assert a1[0] == 2 && a1[0] != 1;
    assert a1[0] > 1;  // Since array is sorted and first element > 1, no element can be 1
    assert forall k :: 0 <= k < a1.Length ==> a1[k] != 1;
    
    var out3 := FindFirstOccurrence(a1, 1);
    assert out3 == -1;
}
