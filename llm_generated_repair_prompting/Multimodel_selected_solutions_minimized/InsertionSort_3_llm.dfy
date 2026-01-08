/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}


lemma SortedMultisetUnique(s1: seq<T>, s2: seq<T>)
    requires Sorted(s1)
    requires Sorted(s2)
    requires multiset(s1) == multiset(s2)
    ensures s1 == s2
{
    if |s1| == 0 {
    } else {
        SortedMultisetUniqueHelper(s1, s2);
    }
}

lemma SortedMultisetUniqueHelper(s1: seq<T>, s2: seq<T>)
    requires |s1| > 0 && |s2| > 0
    requires Sorted(s1)
    requires Sorted(s2)
    requires multiset(s1) == multiset(s2)
    ensures s1 == s2
{
    var m2 := s2[0];
    
    
    assert m2 in multiset(s1);
    
    
    if |s1| > 1 {
        assert s1 == [s1[0]] + s1[1..];
        assert s2 == [s2[0]] + s2[1..];
        assert multiset(s2[1..]) == multiset(s2) - multiset{s2[0]};
        SortedMultisetUniqueHelper(s1[1..], s2[1..]);
    }
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
        invariant Sorted(a[..i])
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant forall k, l :: 0 <= k < l <= i && l != j ==> a[k] <= a[l]
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
    }
}


method {:fuel Sorted,5} TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    assert a[..] == [9, 4, 6, 3, 8];
    InsertionSort(a);
    assert a[..] == [3, 4, 6, 8, 9];
}  

method {:fuel Sorted,3} TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    assert a[..] == [2, 1, 2];
    InsertionSort(a);
    var expected := [1, 2, 2];
    SortedMultisetUnique(a[..], expected);
    assert a[..] ==  [1, 2, 2];
}