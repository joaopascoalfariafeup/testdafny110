
// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures index == -1 <==> forall k :: 0 <= k < arr.Length ==> arr[k] != target
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

// Helper lemma to prove uniqueness of first occurrence
lemma FirstOccurrenceUnique(arr: seq<int>, target: int, idx1: int, idx2: int)
    requires 0 <= idx1 < |arr| && arr[idx1] == target && forall k :: 0 <= k < idx1 ==> arr[k] != target
    requires 0 <= idx2 < |arr| && arr[idx2] == target && forall k :: 0 <= k < idx2 ==> arr[k] != target
    ensures idx1 == idx2
{
    if idx1 < idx2 {
        assert arr[idx1] == target;
        assert idx1 < idx2;
        assert arr[idx1] != target; // contradiction from idx2's precondition
    } else if idx2 < idx1 {
        assert arr[idx2] == target;
        assert idx2 < idx1;
        assert arr[idx2] != target; // contradiction from idx1's precondition
    }
}

// Test cases checked statically.
method FindFirstOccurrenceTest(){
    var a1 := new int[] [2, 5, 5, 5, 6, 6, 8, 9, 9, 9];
    
    // Helper assertions for the array contents
    assert a1[..] == [2, 5, 5, 5, 6, 6, 8, 9, 9, 9];
    assert a1[0] == 2;
    assert a1[1] == 5;
    
    var out1 := FindFirstOccurrence(a1, 5);
    // Prove 5 is in the array, so out1 != -1
    assert a1[1] == 5;
    assert !(forall k :: 0 <= k < a1.Length ==> a1[k] != 5);
    assert out1 != -1;
    assert out1 >= 0;
    // Show that index 1 satisfies the first occurrence property
    assert a1[0] != 5;
    assert forall k :: 0 <= k < 1 ==> a1[k] != 5;
    FirstOccurrenceUnique(a1[..], 5, out1, 1);
    assert out1 == 1;

    assert a1[0] == 2 && a1[1] == 5 && a1[2] == 5 && a1[3] == 5;
    assert a1[4] == 6 && a1[5] == 6 && a1[6] == 8;
    assert a1[7] == 9 && a1[8] == 9 && a1[9] == 9;
    
    var out2 := FindFirstOccurrence(a1, 9);
    // Prove 9 is in the array, so out2 != -1
    assert a1[7] == 9;
    assert !(forall k :: 0 <= k < a1.Length ==> a1[k] != 9);
    assert out2 != -1;
    assert out2 >= 0;
    // Need to show that indices 0-6 don't have 9, and index 7 has 9
    assert a1[0] != 9 && a1[1] != 9 && a1[2] != 9 && a1[3] != 9;
    assert a1[4] != 9 && a1[5] != 9 && a1[6] != 9;
    assert a1[7] == 9;
    assert forall k :: 0 <= k < 7 ==> a1[k] != 9;
    FirstOccurrenceUnique(a1[..], 9, out2, 7);
    assert out2 == 7;

    var out3 := FindFirstOccurrence(a1, 1);
    // Need to show 1 is not in the array
    assert a1[0] != 1 && a1[1] != 1 && a1[2] != 1 && a1[3] != 1 && a1[4] != 1;
    assert a1[5] != 1 && a1[6] != 1 && a1[7] != 1 && a1[8] != 1 && a1[9] != 1;
    assert forall k :: 0 <= k < a1.Length ==> a1[k] != 1;
    // Since no element equals 1, out3 must be -1
    assert out3 == -1;
}
