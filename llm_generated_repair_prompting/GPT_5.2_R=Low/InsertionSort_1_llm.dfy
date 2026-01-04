/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function SwapSeq(s: seq<T>, i: int, j: int): seq<T>
  requires 0 <= i < |s|
  requires 0 <= j < |s|
{
  s[i := s[j]][j := s[i]]
}

lemma SwapSeqMultiset(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(SwapSeq(s, i, j)) == multiset(s)
{
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
{    
    ghost var ms0 := multiset(a[..]);

    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant multiset(a[..]) == ms0
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant 0 <= i < a.Length ==> i + 1 <= a.Length
        invariant multiset(a[..]) == ms0
        invariant forall p, q :: 0 <= p < q < i + 1 ==> q == j || a[p] <= a[q]
      {
        ghost var before := a[..];
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        assert a[..] == SwapSeq(before, j-1, j);
        SwapSeqMultiset(before, j-1, j);
        assert multiset(a[..]) == multiset(before);
        j := j - 1;
      }

      assert forall p, q :: 0 <= p < q < i + 1 ==> a[p] <= a[q]
      {
        if q == j {
          if p == q - 1 {
            assert j == 0 || a[j-1] <= a[j];
            assert a[p] <= a[q];
          } else {
            assert p < q - 1;
            assert a[p] <= a[q-1];
            assert a[q-1] <= a[q];
            assert a[p] <= a[q];
          }
        } else {
          assert a[p] <= a[q];
        }
      }
      assert Sorted(a[..i+1]);
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



