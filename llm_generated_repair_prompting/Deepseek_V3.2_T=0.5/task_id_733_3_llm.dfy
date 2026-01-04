// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures -1 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
  ensures index == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != target
  ensures index != -1 ==> forall k :: 0 <= k < index ==> arr[k] < target
{
    for i := 0 to arr.Length
      invariant 0 <= i <= arr.Length
      invariant forall k :: 0 <= k < i ==> arr[k] < target
    {
        if i < arr.Length {
            if arr[i] == target {
                index := i;
                return;
            }
            else if arr[i] > target {
                index := -1;
                return;
            }
        }
    }
    index := -1;
}

// Test cases checked statically.
method FindFirstOccurrenceTest(){
    var a1 := new int[] [2, 5, 5, 5, 6, 6, 8, 9, 9, 9];
    // Helper assertions to establish array properties
    assert a1[..] == [2, 5, 5, 5, 6, 6, 8, 9, 9, 9];
    assert forall i, j :: 0 <= i < j < a1.Length ==> a1[i] <= a1[j];
    
    var out1 := FindFirstOccurrence(a1, 5);
    // Additional helper assertions to prove out1 == 1
    assert a1[1] == 5;
    assert forall k :: 0 <= k < 1 ==> a1[k] < 5;
    assert out1 == 1;

    var out2 := FindFirstOccurrence(a1, 9);
    // Verify that index 7 is indeed the first occurrence of 9
    assert a1[7] == 9;
    assert forall k :: 0 <= k < 7 ==> a1[k] < 9;
    assert out2 == 7;

    var out3 := FindFirstOccurrence(a1, 1);
    assert out3 == -1;
}

