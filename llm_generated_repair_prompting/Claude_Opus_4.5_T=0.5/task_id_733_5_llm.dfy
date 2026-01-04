// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures index == -1 || (0 <= index < arr.Length)
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

// Lemma: if index is the first occurrence of target, it's unique
lemma FirstOccurrenceUnique(arr: array<int>, target: int, i1: int, i2: int)
    requires 0 <= i1 < arr.Length && arr[i1] == target && forall k :: 0 <= k < i1 ==> arr[k] != target
    requires 0 <= i2 < arr.Length && arr[i2] == target && forall k :: 0 <= k < i2 ==> arr[k] != target
    ensures i1 == i2
{
    if i1 < i2 {
        assert arr[i1] != target; // contradiction from i2's precondition
    } else if i2 < i1 {
        assert arr[i2] != target; // contradiction from i1's precondition
    }
}

// Test cases checked statically.
method FindFirstOccurrenceTest(){
    var a1 := new int[] [2, 5, 5, 5, 6, 6, 8, 9, 9, 9];
    
    // Helper assertions for out1
    assert a1[..] == [2, 5, 5, 5, 6, 6, 8, 9, 9, 9];
    assert a1[0] == 2;
    assert a1[1] == 5;
    assert a1[0] != 5;
    
    var out1 := FindFirstOccurrence(a1, 5);
    // From postcondition: a1[out1] == 5 and forall k :: 0 <= k < out1 ==> a1[k] != 5
    // We know index 1 satisfies this property
    assert a1[1] == 5 && forall k :: 0 <= k < 1 ==> a1[k] != 5;
    // First establish that out1 >= 0 (target 5 exists in array)
    assert a1[1] == 5;  // 5 exists in the array
    // By contrapositive of first postcondition: if exists k such that a1[k] == target, then index != -1
    assert !(forall k :: 0 <= k < a1.Length ==> a1[k] != 5);  // negation of postcondition consequent
    assert out1 != -1;  // so out1 can't be -1 (from first postcondition contrapositive)
    // From the new postcondition: out1 == -1 || (0 <= out1 < a1.Length)
    // Since out1 != -1, we have 0 <= out1 < a1.Length
    assert out1 >= 0;   // therefore out1 >= 0
    // Use lemma to prove uniqueness
    FirstOccurrenceUnique(a1, 5, out1, 1);
    assert out1 == 1;

    // Helper assertions for out2
    assert a1[7] == 9;
    assert a1[0] != 9 && a1[1] != 9 && a1[2] != 9 && a1[3] != 9;
    assert a1[4] != 9 && a1[5] != 9 && a1[6] != 9;
    assert forall k :: 0 <= k < 7 ==> a1[k] != 9;
    
    var out2 := FindFirstOccurrence(a1, 9);
    // We know index 7 satisfies the first occurrence property
    assert a1[7] == 9 && forall k :: 0 <= k < 7 ==> a1[k] != 9;
    // First establish that out2 >= 0 (target 9 exists in array)
    assert a1[7] == 9;  // 9 exists in the array
    assert !(forall k :: 0 <= k < a1.Length ==> a1[k] != 9);
    assert out2 != -1;  // so out2 can't be -1
    assert out2 >= 0;   // therefore out2 >= 0
    FirstOccurrenceUnique(a1, 9, out2, 7);
    assert out2 == 7;

    // Helper assertions for out3
    assert a1[0] == 2;
    assert a1[0] != 1 && a1[1] != 1 && a1[2] != 1 && a1[3] != 1 && a1[4] != 1;
    assert a1[5] != 1 && a1[6] != 1 && a1[7] != 1 && a1[8] != 1 && a1[9] != 1;
    assert forall k :: 0 <= k < a1.Length ==> a1[k] != 1;
    
    var out3 := FindFirstOccurrence(a1, 1);
    // Postcondition says: out3 == -1 ==> forall k :: 0 <= k < a1.Length ==> a1[k] != 1
    // By contrapositive: if exists k such that a1[k] == 1, then out3 != -1
    // We know no element equals 1, so if out3 >= 0, then a1[out3] == 1, contradiction
    // From third postcondition: if out3 >= 0 then a1[out3] == 1
    // But we know forall k :: 0 <= k < a1.Length ==> a1[k] != 1
    // So out3 >= 0 would mean a1[out3] == 1 which contradicts our assertion
    assert !(out3 >= 0);  // because that would mean a1[out3] == 1
    assert out3 == -1;
}

