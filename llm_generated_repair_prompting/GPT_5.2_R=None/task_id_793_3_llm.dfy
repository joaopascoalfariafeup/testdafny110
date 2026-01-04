// Determines the last position of an element 'elem' in a sorted array 'arr'.
// If the element is not in the array, the method returns -1.
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
  requires forall k :: 0 <= k < arr.Length - 1 ==> arr[k] <= arr[k+1]
  ensures pos == -1 || 0 <= pos < arr.Length
  ensures pos != -1 ==> arr[pos] == elem
  ensures pos != -1 ==> forall k :: pos < k < arr.Length ==> arr[k] != elem
  ensures pos == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != elem
{
    // Scan from the end of the array to the begin of the array.
    var i := arr.Length - 1;
    while i >= 0 && arr[i] > elem
      invariant -1 <= i < arr.Length
      invariant forall k :: i < k < arr.Length ==> arr[k] > elem
    {
        i := i - 1;
    }
    if i >= 0 && arr[i] == elem {
        assert forall k :: i < k < arr.Length ==> arr[k] > elem;
        assert forall k :: i < k < arr.Length ==> arr[k] != elem;
        return i;
    }
    assert forall k :: i < k < arr.Length ==> arr[k] > elem;

    if i >= 0 {
        assert arr[i] <= elem;
        assert arr[i] != elem;
        assert arr[i] < elem;

        // In a nondecreasing array, all earlier elements are <= arr[i]
        assert forall k :: 0 <= k <= i ==> arr[k] <= arr[i] by {
          var k :| 0 <= k <= i;
          if k == i {
            // trivial
          } else {
            // use monotonicity from k to i
            assert arr[k] <= arr[i] by {
              var j := k;
              while j < i
                invariant k <= j <= i
                invariant arr[k] <= arr[j]
              {
                assert j < arr.Length - 1; // since j < i and i < arr.Length
                assert arr[j] <= arr[j+1]; // from sortedness
                assert arr[k] <= arr[j+1];
                j := j + 1;
              }
            }
          }
        };

        // Since arr[k] <= arr[i] < elem, we get arr[k] < elem
        assert forall k :: 0 <= k <= i ==> arr[k] < elem;

        assert forall k :: i < k < arr.Length ==> arr[k] > elem;
        assert forall k :: 0 <= k < arr.Length ==> arr[k] != elem;
    } else {
        assert forall k :: 0 <= k < arr.Length ==> arr[k] > elem;
        assert forall k :: 0 <= k < arr.Length ==> arr[k] != elem;
    }
    return -1;
}

// Test cases checked statically.
method LastPositionTest(){
    var a1 := new int[] [1, 1, 1, 2, 3, 4, 4];
    assert a1[..] == [1, 1, 1, 2, 3, 4, 4];

    var out1 := LastPosition(a1, 1);
    assert out1 == 2;

    var out2 := LastPosition(a1, 4);
    assert out2 == 6;

    var out3 := LastPosition(a1, 5);
    assert out3 == -1;

    var out4 := LastPosition(a1, 0);
    assert out3 == -1;
}
