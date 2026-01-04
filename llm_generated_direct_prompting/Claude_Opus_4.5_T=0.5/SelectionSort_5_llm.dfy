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

// Checks if all elements in a[lo..hi] are >= all elements in a[0..lo]
ghost predicate Partitioned(a: array<int>, lo: int)
  reads a
  requires 0 <= lo <= a.Length
{
  forall i, j :: 0 <= i < lo <= j < a.Length ==> a[i] <= a[j]
}

// Checks if sequence is a permutation of another
ghost predicate IsPermutation(s1: seq<int>, s2: seq<int>)
{
  multiset(s1) == multiset(s2)
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
      invariant Partitioned(a, i)
      invariant IsPermutation(a[..], old(a[..]))
    {
        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i <= jMin < a.Length || (jMin == i && j == i + 1)
          invariant i < a.Length ==> i <= jMin < a.Length
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
method testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  SelectionSort(a);
  assert a[..] == [1, 4, 6, 8, 9];
}
