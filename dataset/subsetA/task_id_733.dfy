// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures target !in arr[..] ==> index == -1 
    ensures target in arr[..] ==> 0 <= index < arr.Length && arr[index] == target && target !in arr[..index]
{
    for i := 0 to arr.Length
        invariant target !in arr[..i]
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
    var out1 := FindFirstOccurrence(a1, 5);
    assert a1[1] == 5; // proof helper
    assert out1 == 1;

    var out2 := FindFirstOccurrence(a1, 9);
    assert a1[7] == 9; // proof helper
    assert out2 == 7;

    var out3 := FindFirstOccurrence(a1, 1);
    assert out3 == -1;
}
