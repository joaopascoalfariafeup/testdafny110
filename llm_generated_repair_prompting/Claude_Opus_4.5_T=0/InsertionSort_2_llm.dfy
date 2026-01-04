/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate SortedBetween(a: array<T>, lo: int, hi: int)
    reads a
{
    forall i, j :: 0 <= lo <= i < j < hi <= a.Length ==> a[i] <= a[j]
}

ghost function MultisetSeq(s: seq<T>): multiset<T>
{
    if |s| == 0 then multiset{} else multiset{s[|s|-1]} + MultisetSeq(s[..|s|-1])
}

// Lemma: Two sorted sequences with the same multiset are equal
lemma SortedMultisetUnique(s1: seq<T>, s2: seq<T>)
    requires Sorted(s1)
    requires Sorted(s2)
    requires multiset(s1) == multiset(s2)
    ensures s1 == s2
{
    if |s1| == 0 {
        assert |s2| == 0;
    } else {
        assert |s1| == |s2|;
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
    // Both sequences have the same length since they have the same multiset
    assert |s1| == |s2|;
    
    // The first elements must be equal (both are minimum)
    var min1 := s1[0];
    var min2 := s2[0];
    
    // min1 is in multiset(s2), so it appears in s2
    assert min1 in multiset(s2);
    // Since s2 is sorted and min1 is in s2, and s2[0] is the minimum of s2
    assert min2 <= min1;
    
    // Similarly, min2 is in multiset(s1)
    assert min2 in multiset(s1);
    assert min1 <= min2;
    
    // Therefore min1 == min2
    assert min1 == min2;
    assert s1[0] == s2[0];
    
    if |s1| > 1 {
        // Prove the tails have the same multiset
        assert s1 == [s1[0]] + s1[1..];
        assert s2 == [s2[0]] + s2[1..];
        assert multiset(s1[1..]) == multiset(s1) - multiset{s1[0]};
        assert multiset(s2[1..]) == multiset(s2) - multiset{s2[0]};
        assert multiset(s1[1..]) == multiset(s2[1..]);
        
        // Recursively prove the tails are equal
        SortedMultisetUniqueHelper(s1[1..], s2[1..]);
        assert s1[1..] == s2[1..];
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
        invariant 0 <= j <= i
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant Sorted(a[..j])
        invariant Sorted(a[j..i+1])
        invariant forall k, l :: 0 <= k < j && j + 1 <= l <= i ==> a[k] <= a[l]
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
    }
}


method TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    assert a[..] == [9, 4, 6, 3, 8];
    ghost var original := a[..];
    InsertionSort(a);
    assert multiset(a[..]) == multiset(original);
    assert multiset(a[..]) == multiset([9, 4, 6, 3, 8]);
    assert multiset([3, 4, 6, 8, 9]) == multiset([9, 4, 6, 3, 8]);
    assert Sorted([3, 4, 6, 8, 9]);
    SortedMultisetUnique(a[..], [3, 4, 6, 8, 9]);
    assert a[..] == [3, 4, 6, 8, 9];
}  

method TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    assert a[..] == [2, 1, 2];
    ghost var original := a[..];
    InsertionSort(a);
    assert multiset(a[..]) == multiset(original);
    assert multiset(a[..]) == multiset([2, 1, 2]);
    assert multiset([1, 2, 2]) == multiset([2, 1, 2]);
    assert Sorted([1, 2, 2]);
    SortedMultisetUnique(a[..], [1, 2, 2]);
    assert a[..] ==  [1, 2, 2];
}
