/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

// Checks if array segment a[lo..hi] is sorted
ghost predicate Sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

// Checks if all elements in a[lo..hi] are <= all elements in a[hi..end]
ghost predicate Partitioned(a: array<int>, lo: int, hi: int, end: int)
  reads a
  requires 0 <= lo <= hi <= end <= a.Length
{
  forall i, j :: lo <= i < hi <= j < end ==> a[i] <= a[j]
}

// Checks if sequence s is a permutation of sequence t
ghost predicate IsPermutation(s: seq<int>, t: seq<int>)
{
  multiset(s) == multiset(t)
}

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a, 0, a.Length)
  ensures IsPermutation(a[..], old(a[..]))
{
    // In each iteration, find the minimum value in the unsorted part of the array
    // (on the right) and append it (by swapping) to the sorted part (on the left).
    for i := 0 to a.Length 
      invariant Sorted(a, 0, i)
      invariant Partitioned(a, 0, i, a.Length)
      invariant IsPermutation(a[..], old(a[..]))
    {
        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i <= jMin < a.Length
          invariant i + 1 <= j <= a.Length
          invariant forall k :: i <= k < j ==> a[jMin] <= a[k]
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


// Test case checked statically.
method {:fuel Sorted, 5} {:fuel IsPermutation, 5} testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  SelectionSort(a);
  assert a[..] == [1, 4, 6, 8, 9];
}
