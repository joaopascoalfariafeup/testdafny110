/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
  forall k :: 0 <= k < |s| - 1 ==> s[k] <= s[k+1]
}

lemma MultisetSwapSeq(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
{    
    ghost var init := a[..];

    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant multiset(a[..]) == multiset(init)
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant multiset(a[..]) == multiset(init)
        invariant Sorted(a[..j])
        invariant forall k :: 0 <= k < i ==> (k != j-1 ==> a[k] <= a[k+1])
        decreases j
      {
        ghost var before := a[..];
        assert 0 <= j-1 < a.Length && 0 <= j < a.Length;

        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)

        assert a[..] == before[(j-1) := before[j]][j := before[j-1]];
        calc {
          multiset(a[..]);
          == { assert a[..] == before[(j-1) := before[j]][j := before[j-1]]; }
          multiset(before[(j-1) := before[j]][j := before[j-1]]);
          == { MultisetSwapSeq(before, j-1, j); }
          multiset(before);
        }
        assert multiset(a[..]) == multiset(before);
        assert multiset(a[..]) == multiset(init);

        j := j - 1;
      }

      assert forall k :: 0 <= k < i ==> a[k] <= a[k+1];
      assert Sorted(a[..i+1]);
    }
    assert multiset(a[..]) == multiset(init);
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
