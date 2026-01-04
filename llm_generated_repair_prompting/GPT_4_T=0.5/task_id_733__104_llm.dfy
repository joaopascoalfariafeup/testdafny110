
// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  requires forall k, j :: 0 <= k < j < arr.Length ==> arr[k] <= arr[j]
  ensures 0 <= index < arr.Length ==> arr[index] == target && (forall k :: 0 <= k < index ==> arr[k] < target)
  ensures index == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != target
{
    for i := 0 to arr.Length
      invariant forall k :: 0 <= k < i ==> arr[k] < target
      invariant i <= arr.Length
    {
        if i == arr.Length {
            return -1;
        }
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
    assert a1[..] == [2, 5, 5, 5, 6, 6, 8, 9, 9, 9]; // helper
    var out1 := FindFirstOccurrence(a1, 5);
    assert out1 == -1 || (0 <= out1 < a1.Length && a1[out1] == 5 && (forall k :: 0 <= k < out1 ==> a1[k] < 5));

    var out2 := FindFirstOccurrence(a1, 9);
    assert out2 == -1 || (0 <= out2 < a1.Length && a1[out2] == 9 && (forall k :: 0 <= k < out2 ==> a1[k] < 9));

    var out3 := FindFirstOccurrence(a1, 1);
    assert out3 == -1 ==> forall k :: 0 <= k < a1.Length ==> a1[k] != 1;
}

