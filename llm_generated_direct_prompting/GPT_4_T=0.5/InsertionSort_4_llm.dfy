/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

// Auxiliary function to check if a sequence is sorted.
function IsSorted(s: seq<T>): bool
{
    forall k :: 0 <= k < |s|-1 ==> s[k] <= s[k+1]
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a    
    ensures IsSorted(a[..]) // the array is sorted after the method call
    ensures forall k :: 0 <= k < a.Length ==> a[..][k] in old(a[..]) // the array contains the same elements as before
    ensures forall v :: v in old(a[..]) ==> v in a[..] // the array contains the same elements as before
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length // 'i' is within array bounds
        invariant IsSorted(a[..i]) // the first 'i' elements are sorted
        invariant forall k :: 0 <= k < i ==> a[..][k] in old(a[..]) // the first 'i' elements are in the original array
        invariant forall v :: v in old(a[..]) ==> v in a[..] // all original elements are in the array
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i // 'j' is within array bounds
        invariant IsSorted(a[..j]) && (j == i || a[j-1] <= a[j]) // the first 'j' elements are sorted
        invariant forall k :: 0 <= k < j ==> a[..][k] in old(a[..]) // the first 'j' elements are in the original array
        invariant forall v :: v in old(a[..]) ==> v in a[..] // all original elements are in the array
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
