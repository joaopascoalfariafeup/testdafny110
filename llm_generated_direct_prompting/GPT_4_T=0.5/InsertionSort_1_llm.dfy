/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

// Auxiliary function to check if a sequence is sorted.
ghost function IsSorted(s: seq<T>): bool {
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures a != null ==> IsSorted(a[..])    
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant IsSorted(a[..i])
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant IsSorted(a[..j]) && IsSorted(a[j..i]) && forall k :: j <= k < i ==> a[j-1] <= a[k]
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

