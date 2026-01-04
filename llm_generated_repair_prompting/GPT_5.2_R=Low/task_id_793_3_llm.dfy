// Determines the last position of an element 'elem' in a sorted array 'arr'.
// If the element is not in the array, the method returns -1.
predicate SortedNondecreasing(arr: array<int>)
  reads arr
{
  forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
}

// Helper lemmas to establish SortedNondecreasing in tests from adjacent ordering
lemma LemmaLeFromAdjacent(arr: array<int>, i: int, j: int)
  requires arr != null
  requires 0 <= i <= j < arr.Length
  requires forall k :: 0 <= k < arr.Length - 1 ==> arr[k] <= arr[k+1]
  ensures arr[i] <= arr[j]
  reads arr
  decreases j - i
{
  if i == j {
  } else {
    LemmaLeFromAdjacent(arr, i, j-1);
    assert arr[j-1] <= arr[j];
  }
}

lemma AdjacentSortedImpliesSorted(arr: array<int>)
  requires arr != null
  requires forall k :: 0 <= k < arr.Length - 1 ==> arr[k] <= arr[k+1]
  ensures SortedNondecreasing(arr)
  reads arr
{
  assert forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j] by {
    LemmaLeFromAdjacent(arr, i, j);
  }
}

method LastPosition(arr: array<int>, elem: int) returns (pos: int)
  requires SortedNondecreasing(arr)
  ensures -1 <= pos < arr.Length
  ensures pos == -1 <==> (forall k :: 0 <= k < arr.Length ==> arr[k] != elem)
  ensures 0 <= pos ==> arr[pos] == elem
  // pos is the last (greatest) index where elem occurs
  ensures 0 <= pos ==> (forall k :: 0 <= k < arr.Length && arr[k] == elem ==> k <= pos)
  // In a sorted array, everything after the last occurrence is strictly larger
  ensures 0 <= pos ==> (forall k :: pos < k < arr.Length ==> arr[k] > elem)
  // Characterization of "last occurrence" boundary
  ensures 0 <= pos ==> (pos == arr.Length - 1 || arr[pos + 1] > elem)
{
    // Scan from the end of the array to the begin of the array.
    var i := arr.Length - 1;
    while i >= 0 && arr[i] > elem
      invariant -1 <= i < arr.Length
      invariant 0 <= i + 1 <= arr.Length
      invariant forall k :: i < k < arr.Length ==> arr[k] > elem
      decreases i + 1
    {
        i := i - 1;
    }

    // From loop exit:
    assert i < 0 || arr[i] <= elem;

    if i >= 0 && arr[i] == elem {
        // Boundary property for the last occurrence
        if i < arr.Length - 1 {
          assert arr[i + 1] > elem; // from invariant with k := i+1
        }
        return i;
    }

    // Prove element is absent when returning -1
    if i < 0 {
      // then forall k, -1 < k < Length ==> arr[k] > elem, so arr[k] != elem
      assert forall k :: 0 <= k < arr.Length ==> arr[k] != elem by {
        assert -1 < k < arr.Length;
        assert arr[k] > elem;
      }
    } else {
      // Here i >= 0 and arr[i] != elem, but arr[i] <= elem, hence arr[i] < elem
      assert arr[i] < elem;

      // For k > i: arr[k] > elem by invariant, so != elem
      // For k <= i: sortedness gives arr[k] <= arr[i] < elem, so != elem
      assert forall k :: 0 <= k < arr.Length ==> arr[k] != elem by {
        if k <= i {
          if k < i {
            assert arr[k] <= arr[i]; // from SortedNondecreasing with (k,i)
          } else {
            assert arr[k] == arr[i];
          }
          assert arr[k] < elem;
        } else {
          assert i < k < arr.Length;
          assert arr[k] > elem;
        }
      }
    }

    return -1;
}

// Test cases checked statically.
method LastPositionTest(){
    var a1 := new int[] [1, 1, 1, 2, 3, 4, 4];
    // Help Dafny use the concrete contents of a1
    assert a1[..] == [1, 1, 1, 2, 3, 4, 4];

    // Establish sortedness from adjacent comparisons
    assert a1[0] <= a1[1];
    assert a1[1] <= a1[2];
    assert a1[2] <= a1[3];
    assert a1[3] <= a1[4];
    assert a1[4] <= a1[5];
    assert a1[5] <= a1[6];
    assert forall k :: 0 <= k < a1.Length - 1 ==> a1[k] <= a1[k+1] by {
      if k == 0 { assert a1[0] <= a1[1]; }
      else if k == 1 { assert a1[1] <= a1[2]; }
      else if k == 2 { assert a1[2] <= a1[3]; }
      else if k == 3 { assert a1[3] <= a1[4]; }
      else if k == 4 { assert a1[4] <= a1[5]; }
      else { assert k == 5; assert a1[5] <= a1[6]; }
    }
    AdjacentSortedImpliesSorted(a1);
    assert SortedNondecreasing(a1);

    var out1 := LastPosition(a1, 1);
    assert out1 == 2;

    var out2 := LastPosition(a1, 4);
    assert out2 == 6;

    var out3 := LastPosition(a1, 5);
    assert out3 == -1;

    var out4 := LastPosition(a1, 0);
    assert out3 == -1;
}
