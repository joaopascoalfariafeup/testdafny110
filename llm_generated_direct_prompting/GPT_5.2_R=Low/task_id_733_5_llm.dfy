predicate Sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

lemma SortedLowerBoundFrom(a: array<int>, i: int)
  requires Sorted(a)
  requires 0 <= i < a.Length
  ensures forall k :: i <= k < a.Length ==> a[i] <= a[k]
{
  forall k | i <= k < a.Length
    ensures a[i] <= a[k]
  {
    if k == i {
    } else {
      assert 0 <= i < k < a.Length;
      assert a[i] <= a[k];
    }
  }
}

lemma SortedGreaterFrom(a: array<int>, i: int, target: int)
  requires Sorted(a)
  requires 0 <= i < a.Length
  requires a[i] > target
  ensures forall k :: i <= k < a.Length ==> a[k] > target
{
  SortedLowerBoundFrom(a, i);
  assert forall k :: i <= k < a.Length ==> a[i] <= a[k];
  forall k | i <= k < a.Length
    ensures a[k] > target
  {
    assert a[i] <= a[k];
    assert target < a[k];
  }
}

// Finds the index of the first occurrence of a target in a sorted array.
// If the target is not in the array, returns -1.
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  requires Sorted(arr)
  ensures index == -1 || 0 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
  ensures index != -1 ==> (forall k :: 0 <= k < index ==> arr[k] != target)
  ensures index == -1 ==> (forall k :: 0 <= k < arr.Length ==> arr[k] != target)
{
    for i := 0 to arr.Length
      invariant 0 <= i <= arr.Length
      invariant forall k :: 0 <= k < i ==> arr[k] != target
    {
        if arr[i] == target {
            return i;
        }
        else if arr[i] > target {
            SortedGreaterFrom(arr, i, target);
            assert forall k :: i <= k < arr.Length ==> arr[k] != target;
            assert forall k :: 0 <= k < arr.Length ==> arr[k] != target;
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

