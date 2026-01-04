/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate SortedSeq(s: seq<T>)
{
  forall k :: 0 <= k < |s| - 1 ==> s[k] <= s[k+1]
}

predicate AdjSortedExcept(a: array<T>, n: int, ex: int)
  requires 0 <= n <= a.Length
{
  forall k :: 0 <= k < n - 1 ==> k == ex || a[k] <= a[k+1]
}


// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures SortedSeq(a[..])
    ensures multiset(a[..]) == old(multiset(a[..]))
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant SortedSeq(a[..i])
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant AdjSortedExcept(a, i+1, j-1)
        invariant multiset(a[..]) == old(multiset(a[..]))
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
      assert AdjSortedExcept(a, i+1, j-1);
      assert j == 0 || a[j-1] <= a[j];
      assert SortedSeq(a[..i+1]) by {
        assert forall k :: 0 <= k < i ==> a[k] <= a[k+1] by {
          intro k;
          if k == j-1 {
            assert j > 0 ==> a[j-1] <= a[j];
          } else {
            assert k == j-1 || a[k] <= a[k+1];
          }
        }
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
