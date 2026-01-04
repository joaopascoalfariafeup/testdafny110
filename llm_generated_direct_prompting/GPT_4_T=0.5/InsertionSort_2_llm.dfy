/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

// Auxiliary function to determine if a sequence is sorted
ghost function IsSorted(s: seq<T>): bool
    reads s
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i+1]
}

// Auxiliary function to determine if two sequences are permutations of each other
ghost function IsPermutation(s1: seq<T>, s2: seq<T>): bool
    reads s1, s2
{
    |s1| == |s2| && forall v :: v in s1 ==> v in s2
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a    
    ensures old(IsPermutation(a[..], a[..]))  // the sorted sequence is a permutation of the input sequence
    ensures IsSorted(a[..])  // the array is sorted in non-decreasing order
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant IsPermutation(old(a[..]), a[..])  // the current sequence is a permutation of the input sequence
        invariant IsSorted(a[..i])  // the left part of the array is sorted
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
          invariant 0 <= j <= i
          invariant IsPermutation(old(a[..i+1]), a[..i+1])  // the current sequence is a permutation of the initial sequence
          invariant IsSorted(a[..j]) && (j == i || a[j-1] <= a[i])  // the left part of the array is sorted and the element at 'i' is in the correct position
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

