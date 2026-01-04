/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

// Predicate to check if a sequence is sorted
ghost predicate Sorted(s: seq<T>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Predicate to check if two sequences are permutations of each other
ghost predicate SameElements(s1: seq<T>, s2: seq<T>)
{
    multiset(s1) == multiset(s2)
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures Sorted(a[..])
    ensures SameElements(a[..], old(a[..]))
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
        invariant Sorted(a[..i])
        invariant SameElements(a[..], old(a[..]))
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant SameElements(a[..], old(a[..]))
        invariant forall k, l :: 0 <= k < l <= i && l != j ==> a[k] <= a[l]
        invariant forall k :: j < k <= i ==> a[j] <= a[k]
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
    }
}


method {:fuel Sorted,5} {:fuel SameElements,5} TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    InsertionSort(a);
    assert a[..] == [3, 4, 6, 8, 9];
}  

method {:fuel Sorted,3} {:fuel SameElements,3} TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    InsertionSort(a);
    assert a[..] ==  [1, 2, 2];
}



