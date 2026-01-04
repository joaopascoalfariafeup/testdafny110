/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
    // In each iteration, find the minimum value in the unsorted part of the array
    // (on the right) and append it (by swapping) to the sorted part (on the left).
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant forall p, q :: 0 <= p < i && i <= q < a.Length ==> a[p] <= a[q]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
        ghost var ms0 := multiset(a[..]);

        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i + 1 <= j <= a.Length
          invariant i <= jMin < a.Length
          invariant forall k :: i <= k < j ==> a[jMin] <= a[k]
        {
            if a[j] < a[jMin] {
                jMin := j;
            }
        } 

        ghost var minVal := a[jMin];
        assert forall k :: i <= k < a.Length ==> minVal <= a[k];

        // Swap it with the first unsorted element
        if jMin != i {
          a[i], a[jMin] := a[jMin], a[i]; 
        }

        assert a[i] == minVal;
        assert forall q :: i + 1 <= q < a.Length ==> a[i] <= a[q];
        assert forall p :: 0 <= p < i ==> a[p] <= a[i];
        assert Sorted(a[..i + 1]);

        assert forall p, q :: 0 <= p < i + 1 && i + 1 <= q < a.Length ==> a[p] <= a[q];

        assert multiset(a[..]) == ms0;
    }
}


// Test case checked statically.
method testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  SelectionSort(a);
  assert a[..] == [1, 4, 6, 8, 9];
}
