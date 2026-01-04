/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

// Auxiliary predicate that checks if a sequence 's' is sorted. 
ghost predicate IsSorted(s: seq<T>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] 
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a    
    ensures IsSorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
      invariant IsSorted(a[..i]) 
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant forall l, r :: 0 <= l < r <= i && r != j ==> a[l] <= a[r] 
        invariant multiset(a[..]) == multiset(old(a[..]))
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
    }
}


method TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    assert a[..] == [9, 4, 6, 3, 8]; // helper
    InsertionSort(a);
    assert a[..] == [3, 4, 6, 8, 9];
}  

method TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    assert a[..] == [2, 1, 2]; // helper
    InsertionSort(a);
    SortingUniqueness(a[..],  [1, 2, 2]); // helper
    assert a[..] ==  [1, 2, 2];
}

// State and prove by induction the property that, if two sequences are sorted and have 
// the same multiset of elements, then they must be identical (so sorting has a unique solution). 
lemma SortingUniqueness(a: seq<T>, b: seq<T>)
    requires IsSorted(a) && IsSorted(b) && multiset(a) == multiset(b) 
    ensures a == b
{
    if |a| > 1 {
      // Only key steps of proof by induction are provided here.
      assert forall i :: 0 <= i < |a| ==> a[i] in multiset(a); 
      assert forall i :: 0 <= i < |b| ==> b[i] in multiset(b); 
      assert a[0] == b[0];
      assert a == [a[0]] + a[1..];
      assert b == [b[0]] + b[1..];
      SortingUniqueness(a[1..], b[1..]);
    }
}
