// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.

ghost predicate SortedNondecreasing(a: array<int>)
  reads a
{
  forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k+1]
}

lemma PrefixLeqSuffix(a: array<int>, i: int, j: int)
  requires SortedNondecreasing(a)
  requires 0 <= i <= j < a.Length
  ensures a[i] <= a[j]
{
  if i == j {
  } else {
    PrefixLeqSuffix(a, i, j - 1);
    assert a[j - 1] <= a[j];
  }
}

method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  requires SortedNondecreasing(arr)
  ensures index == -1 || 0 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
  ensures index != -1 ==> forall j :: 0 <= j < index ==> arr[j] != target
  ensures index == -1 ==> forall j :: 0 <= j < arr.Length ==> arr[j] != target
{
    for i := 0 to arr.Length
      invariant 0 <= i <= arr.Length
      invariant forall j :: 0 <= j < i ==> arr[j] != target
    {
        if arr[i] == target {
            return i;
        }
        else if arr[i] > target {
            // Everything before i is not target (loop invariant)
            assert forall j :: 0 <= j < i ==> arr[j] != target;

            // Everything from i onward is > target, by sortedness from arr[i] > target
            assert forall j :: i <= j < arr.Length ==> arr[j] > target by {
              forall j | i <= j < arr.Length
                ensures arr[j] > target
              {
                if j == i {
                  assert arr[j] > target;
                } else {
                  PrefixLeqSuffix(arr, i, j);
                  assert arr[i] <= arr[j];
                  assert arr[i] > target;
                  assert arr[j] > target;
                }
              }
            }

            // Therefore no position holds target
            assert forall j :: 0 <= j < arr.Length ==> arr[j] != target by {
              forall j | 0 <= j < arr.Length
                ensures arr[j] != target
              {
                if j < i {
                  assert arr[j] != target; // invariant
                } else {
                  assert arr[j] > target;  // suffix fact
                  assert arr[j] != target;
                }
              }
            }
            return -1;
        }
    }
    // If we reached here, we've established arr[j] != target for all j < arr.Length
    return -1;
}

// Test cases checked statically.
method FindFirstOccurrenceTest(){
    var a1 := new int[] [2, 5, 5, 5, 6, 6, 8, 9, 9, 9];
    assert SortedNondecreasing(a1);

    var out1 := FindFirstOccurrence(a1, 5);
    assert out1 == 1;

    var out2 := FindFirstOccurrence(a1, 9);
    assert a1[7] == 9;
    assert out2 == 7;

    var out3 := FindFirstOccurrence(a1, 1);
    assert out3 == -1;
}
