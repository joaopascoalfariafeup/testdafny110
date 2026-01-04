/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures IsSorted(a) 
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    // In each iteration, find the minimum value in the unsorted part of the array
    // (on the right) and append it (by swapping) to the sorted part (on the left).
    for i := 0 to a.Length 
      invariant forall l, r :: 0 <= l < i && l < r < a.Length ==> a[l] <= a[r] // a[..i] sorted and <= a[i..]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i <= jMin < a.Length
          invariant forall k :: i <= k < j ==> a[k] >= a[jMin]
        {
            if a[j] < a[jMin] {
                jMin := j;
            }
        } 
        // Swap it with the first unsorted element
        if jMin != i {
          a[i], a[jMin] := a[jMin], a[i]; 
        }
    }
}

// Auxiliary predicate that checks if an array 'a' is sorted.
ghost predicate IsSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] 
}

// Test case checked statically.
method testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  assert a[..] == [9, 4, 6, 1, 8]; // helper 
  SelectionSort(a);
  assert a[..] == [1, 4, 6, 8, 9];
}