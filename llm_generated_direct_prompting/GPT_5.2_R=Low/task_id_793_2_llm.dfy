// Determines the last position of an element 'elem' in a sorted array 'arr'.
// If the element is not in the array, the method returns -1.
predicate Sorted(arr: array<int>)
  reads arr
{
  forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
}

method LastPosition(arr: array<int>, elem: int) returns (pos: int)
  requires Sorted(arr)
  ensures pos == -1 ==> (forall k :: 0 <= k < arr.Length ==> arr[k] != elem)
  ensures pos != -1 ==> 0 <= pos < arr.Length
  ensures pos != -1 ==> arr[pos] == elem
  ensures pos != -1 ==> (forall k :: pos < k < arr.Length ==> arr[k] != elem)
{
    // Scan from the end of the array to the begin of the array.
    var i := arr.Length - 1;
    while i >= 0 && arr[i] > elem
      invariant -1 <= i < arr.Length
      invariant Sorted(arr)
      invariant forall k :: i < k < arr.Length ==> arr[k] > elem
      decreases i + 1
    {        
        i := i - 1;
    }
    if i >= 0 && arr[i] == elem {
        return i;
    }

    if i < 0 {
      assert forall k :: 0 <= k < arr.Length ==> arr[k] > elem;
      assert forall k :: 0 <= k < arr.Length ==> arr[k] != elem;
      return -1;
    } else {
      // Here: i >= 0 and not(arr[i] == elem), and loop exit implies arr[i] <= elem
      assert arr[i] <= elem;
      assert arr[i] < elem;

      assert forall k :: 0 <= k <= i ==> arr[k] <= arr[i] by {
        forall k | 0 <= k <= i
          ensures arr[k] <= arr[i]
        {
          if k == i {
          } else {
            assert 0 <= k < i < arr.Length;
            assert arr[k] <= arr[i];
          }
        }
      }

      assert forall k :: 0 <= k <= i ==> arr[k] != elem by {
        forall k | 0 <= k <= i
          ensures arr[k] != elem
        {
          assert arr[k] <= arr[i];
          assert arr[i] < elem;
          assert arr[k] < elem;
        }
      }

      assert forall k :: i < k < arr.Length ==> arr[k] > elem;
      assert forall k :: i < k < arr.Length ==> arr[k] != elem;

      assert forall k :: 0 <= k < arr.Length ==> arr[k] != elem;
      return -1;
    }
}

// Test cases checked statically.
method LastPositionTest(){
    var a1 := new int[] [1, 1, 1, 2, 3, 4, 4];

    var out1 := LastPosition(a1, 1);
    assert out1 == 2;

    var out2 := LastPosition(a1, 4);
    assert out2 == 6;

    var out3 := LastPosition(a1, 5);
    assert out3 == -1;

    var out4 := LastPosition(a1, 0);
    assert out3 == -1;
}
