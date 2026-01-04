/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  requires a != null
  ensures forall k :: 0 <= k < a.Length-1 ==> a[k] <= a[k+1]  // The array is sorted in non-decreasing order
  ensures old(a).Perm(a) // The array contains the same elements as before, only reordered
{
    // In each iteration, find the minimum value in the unsorted part of the array
    // (on the right) and append it (by swapping) to the sorted part (on the left).
    for i := 0 to a.Length 
      invariant 0 <= i <= a.Length  // 'i' is always within the array bounds
      invariant forall k :: 0 <= k < i ==> forall l :: i <= l < a.Length ==> a[k] <= a[l]  // The left part of the array is sorted and all its elements are not greater than the elements in the right part
      invariant old(a[0..i]).Perm(a[0..i]) && old(a[i..]).Perm(a[i..])  // The elements in each part of the array (left and right) are a permutation of the original elements in that part
    {
        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i < j <= a.Length  // 'j' is always within the array bounds
          invariant i <= jMin < j  // 'jMin' is always within the array bounds
          invariant forall k :: i <= k < j ==> a[jMin] <= a[k]  // 'jMin' index points to the smallest element in the unsorted part of the array
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
