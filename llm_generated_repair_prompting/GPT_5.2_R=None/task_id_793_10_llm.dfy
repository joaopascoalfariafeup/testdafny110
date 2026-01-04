// Determines the last position of an element 'elem' in a sorted array 'arr'.
// If the element is not in the array, the method returns -1.
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
  requires arr != null
  requires forall k :: 0 <= k < arr.Length - 1 ==> arr[k] <= arr[k+1]
  ensures pos == -1 || 0 <= pos < arr.Length
  ensures pos != -1 ==> arr[pos] == elem
  ensures pos != -1 ==> forall k :: pos < k < arr.Length ==> arr[k] != elem
  ensures pos == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != elem
  // Strengthen: if elem occurs, pos is the maximum index where it occurs
  ensures pos != -1 ==> forall k :: 0 <= k < arr.Length ==> (arr[k] == elem ==> k <= pos)
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
        // Also: for any k > i, invariant gives arr[k] > elem, so no k>i can be elem
        assert forall k :: 0 <= k < arr.Length ==> (arr[k] == elem ==> k <= i) by
        {
          forall k | 0 <= k < arr.Length
            ensures arr[k] == elem ==> k <= i
          {
            if i < k {
              assert arr[k] > elem;
            }
          }
        }
        return i;
    }
    assert forall k :: i < k < arr.Length ==> arr[k] > elem;

    if i >= 0 {
        assert arr[i] <= elem;
        assert arr[i] != elem;
        assert arr[i] < elem;

        // In a nondecreasing array, all earlier elements are <= arr[i]
        assert forall k :: 0 <= k <= i ==> arr[k] <= arr[i] by
        {
          forall k | 0 <= k <= i
            ensures arr[k] <= arr[i]
          {
            if k == i {
            } else {
              var j := k;
              while j < i
                invariant k <= j <= i
                invariant arr[k] <= arr[j]
              {
                assert j < arr.Length - 1;   // since j < i and i < arr.Length
                assert arr[j] <= arr[j+1];   // from sortedness
                assert arr[k] <= arr[j+1];   // transitivity
                j := j + 1;
              }
              assert j == i;
            }
          }
        }

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

    // Help the verifier use concrete facts about a1's contents
    assert a1.Length == 7;
    assert a1[0] == 1 && a1[1] == 1 && a1[2] == 1 && a1[3] == 2 && a1[4] == 3 && a1[5] == 4 && a1[6] == 4;

    // Provide the sortedness fact needed by LastPosition's precondition
    assert forall k :: 0 <= k < a1.Length - 1 ==> a1[k] <= a1[k+1];

    var out1 := LastPosition(a1, 1);
    // Use postcondition + concrete array contents to pin down the exact index
    assert out1 != -1;
    assert a1[out1] == 1;
    assert out1 <= 2; // from "maximum index" postcondition with witness k=2
    assert 2 <= out1 by
    {
      // if out1 < 2, then k=2 contradicts "no elem after out1"
      if out1 < 2 {
        assert out1 < 2 < a1.Length;
        assert a1[2] == 1;
        assert forall k :: out1 < k < a1.Length ==> a1[k] != 1;
      }
    }
    assert out1 == 2;

    var out2 := LastPosition(a1, 4);
    assert out2 != -1;
    assert a1[out2] == 4;
    assert out2 <= 6; // from "maximum index" postcondition with witness k=6
    assert 6 <= out2 by
    {
      if out2 < 6 {
        assert out2 < 6 < a1.Length;
        assert a1[6] == 4;
        assert forall k :: out2 < k < a1.Length ==> a1[k] != 4;
      }
    }
    assert out2 == 6;

    var out3 := LastPosition(a1, 5);
    assert out3 == -1;

    var out4 := LastPosition(a1, 0);
    assert out3 == -1;
}
