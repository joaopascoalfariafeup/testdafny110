/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function MultisetOf(s: seq<T>): multiset<T>
{
    multiset(s)
}

// Lemma: Two sorted sequences with the same multiset must be equal
lemma SortedMultisetUnique(s1: seq<T>, s2: seq<T>)
    requires Sorted(s1)
    requires Sorted(s2)
    requires multiset(s1) == multiset(s2)
    ensures s1 == s2
{
    if |s1| == 0 {
        assert |multiset(s2)| == |multiset(s1)| == 0;
        assert |s2| == 0;
    } else {
        assert |multiset(s1)| == |s1|;
        assert |multiset(s2)| == |s2|;
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
    // The minimum element must be the same (first element in both sorted sequences)
    var m1 := s1[0];
    var m2 := s2[0];
    
    // m1 is in multiset(s2), so m1 is somewhere in s2
    assert m1 in multiset(s2);
    // Since s2 is sorted and m1 is in s2, and s2[0] is the minimum, m1 >= s2[0]
    
    // Similarly m2 is in multiset(s1)
    assert m2 in multiset(s1);
    // Since s1 is sorted and m2 is in s1, and s1[0] is the minimum, m2 >= s1[0]
    
    // So m1 >= m2 and m2 >= m1, thus m1 == m2
    assert m1 == m2;
    
    if |s1| > 1 {
        assert s1 == [s1[0]] + s1[1..];
        assert s2 == [s2[0]] + s2[1..];
        assert multiset(s1[1..]) == multiset(s1) - multiset{s1[0]};
        assert multiset(s2[1..]) == multiset(s2) - multiset{s2[0]};
        assert multiset(s1[1..]) == multiset(s2[1..]);
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
        invariant 0 <= j <= i
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant forall k, l :: 0 <= k < l <= i && l != j ==> a[k] <= a[l]
        invariant forall k :: j < k <= i ==> a[j] <= a[k]
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
    }
}


method {:fuel Sorted,5} TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    assert a[..] == [9, 4, 6, 3, 8];
    assert multiset(a[..]) == multiset{9, 4, 6, 3, 8};
    InsertionSort(a);
    var expected := [3, 4, 6, 8, 9];
    assert Sorted(expected);
    assert multiset(expected) == multiset{3, 4, 6, 8, 9};
    assert multiset{9, 4, 6, 3, 8} == multiset{3, 4, 6, 8, 9};
    SortedMultisetUnique(a[..], expected);
    assert a[..] == [3, 4, 6, 8, 9];
}  

method {:fuel Sorted,3} TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    assert a[..] == [2, 1, 2];
    assert multiset(a[..]) == multiset{2, 1, 2};
    InsertionSort(a);
    var expected := [1, 2, 2];
    assert Sorted(expected);
    assert multiset(expected) == multiset{1, 2, 2};
    assert multiset{2, 1, 2} == multiset{1, 2, 2};
    SortedMultisetUnique(a[..], expected);
    assert a[..] ==  [1, 2, 2];
}
