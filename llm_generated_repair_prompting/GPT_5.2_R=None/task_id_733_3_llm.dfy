// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  requires forall i :: 0 <= i < arr.Length - 1 ==> arr[i] <= arr[i+1]
  ensures index == -1 || 0 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
  ensures index != -1 ==> forall j :: 0 <= j < index ==> arr[j] != target
  ensures index == -1 ==> forall j :: 0 <= j < arr.Length ==> arr[j] != target
{
    for i := 0 to arr.Length
      invariant 0 <= i <= arr.Length
      invariant forall j :: 0 <= j < i ==> arr[j] != target
      // If some element before i is already > target, then by sortedness all elements from i onward are > target
      invariant forall k :: 0 <= k < i && arr[k] > target ==> forall j :: i <= j < arr.Length ==> arr[j] > target
    {
        if arr[i] == target {
            return i;
        }
        else if arr[i] > target {
            // Prove "target not in array" on this early return
            assert forall j :: 0 <= j < i ==> arr[j] != target; // from invariant

            // Establish the "all later elements are > target" fact from the invariant, using k := i
            assert forall j :: i+1 <= j < arr.Length ==> arr[j] > target by {
              assert (forall k :: 0 <= k < i+1 && arr[k] > target ==> forall j :: i+1 <= j < arr.Length ==> arr[j] > target); // invariant at i+1
              assert 0 <= i < i+1;
              assert arr[i] > target;
            }

            // Now combine arr[i] > target with the above suffix property
            assert forall j :: i <= j < arr.Length ==> arr[j] > target by {
              assert forall j :: i+1 <= j < arr.Length ==> arr[j] > target;
            }

            assert forall j :: 0 <= j < arr.Length ==> arr[j] != target;
            return -1;
        }
    }
    // If we reached here, we've established arr[j] != target for all j < arr.Length
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
