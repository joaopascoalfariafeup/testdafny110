/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

// Ghost function to check if a sequence is sorted
ghost function IsSorted(a: seq<int>): bool
{
  forall i | 0 <= i < |a|-1 :: a[i] <= a[i+1]
}

// Ghost function to count the number of occurrences of a value in a sequence
ghost function Count(a: seq<int>, val: int): nat
{
  if |a| == 0 then 0
  else (if a[0] == val then 1 else 0) + Count(a[1..], val)
}

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures forall i :: 0 <= i < a.Length ==> Count(old(a[..]), a[i]) == Count(a[..], a[i])
{
    // In each iteration, find the minimum value in the unsorted part of the array
    // (on the right) and append it (by swapping) to the sorted part (on the left).
    for i := 0 to a.Length 
      invariant 0 <= i <= a.Length
      invariant IsSorted(a[..i])
      invariant forall k :: 0 <= k < i ==> Count(old(a[..]), a[k]) == Count(a[..], a[k])
      invariant forall k1, k2 :: 0 <= k1 < i <= k2 < a.Length ==> a[k1] <= a[k2]
    {
        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i <= j <= a.Length
          invariant i <= jMin < a.Length
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
