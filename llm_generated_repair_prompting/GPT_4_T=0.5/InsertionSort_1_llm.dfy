/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

// Function to check if an array is sorted
ghost function IsSorted(a: array<T>, l: int, r: int): bool
  reads a
{
  forall i :: 0 <= i < r-l ==> a[l+i] <= a[l+i+1]
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a    
    ensures IsSorted(a, 0, a.Length-1)
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant IsSorted(a, 0, i-1)
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
          invariant 0 < j <= i
          invariant IsSorted(a, 0, j-1)
          invariant IsSorted(a, j, i)
          invariant forall k :: j <= k <= i ==> a[k] >= a[j-1]
          decreases j
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
    }
}


method TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    InsertionSort(a);
    assert a[..] == [3, 4, 6, 8, 9];
}  

method TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    InsertionSort(a);
    assert a[..] ==  [1, 2, 2];
}



