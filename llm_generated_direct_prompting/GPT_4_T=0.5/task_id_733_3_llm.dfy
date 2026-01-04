// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  requires forall k, j :: 0 <= k < j < arr.Length ==> arr[k] <= arr[j] // array is sorted in non-decreasing order
  ensures 0 <= index < arr.Length ==> arr[index] == target // if index is in array bounds, it points to target
  ensures index == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != target // if index is -1, target is not in array
{
    for i := 0 to arr.Length
      invariant 0 <= i <= arr.Length // i is within array bounds
      invariant forall k :: 0 <= k < i ==> arr[k] != target // elements before i are not target
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
    assert out1 == 1;

    var out2 := FindFirstOccurrence(a1, 9);
    assert a1[7] == 9;
    assert out2 == 7;

    var out3 := FindFirstOccurrence(a1, 1);
    assert out3 == -1;
}

