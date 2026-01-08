// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
predicate SortedNonDecreasing(arr: array<int>)
  reads arr
{
  forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
}

method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  requires SortedNonDecreasing(arr)
  ensures -1 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
  ensures index != -1 ==> forall k :: 0 <= k < index ==> arr[k] != target
  ensures index == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != target
{
    for i := 0 to arr.Length
      invariant forall k :: 0 <= k < i ==> arr[k] < target
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

    assert a1[7] == 9;

    var out1 := FindFirstOccurrence(a1, 5);


    var out2 := FindFirstOccurrence(a1, 9);
    assert out2 == 7;

    var out3 := FindFirstOccurrence(a1, 1);
    assert out3 == -1;
}