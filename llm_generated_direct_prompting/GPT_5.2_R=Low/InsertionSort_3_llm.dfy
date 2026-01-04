/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate AdjSorted(s: seq<T>)
{
  forall k :: 0 <= k < |s| - 1 ==> s[k] <= s[k+1]
}

predicate AdjSortedExceptAt(s: seq<T>, k: int)
{
  forall t :: 0 <= t < |s| - 1 && t != k ==> s[t] <= s[t+1]
}

function Swap(s: seq<T>, i: int, j: int): seq<T>
  requires 0 <= i < |s|
  requires 0 <= j < |s|
{
  s[i := s[j]][j := s[i]]
}

lemma MultisetSwapPreserves(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(Swap(s, i, j)) == multiset(s)
{
}

lemma SwapMovesInversionLeft(s: seq<T>, j: int)
  requires 0 < j < |s|
  requires AdjSortedExceptAt(s, j-1)
  requires s[j-1] > s[j]
  ensures AdjSortedExceptAt(Swap(s, j-1, j), if j == 1 then -1 else j-2)
{
}

lemma AdjSortedFromExceptAt(s: seq<T>, k: int)
  requires AdjSortedExceptAt(s, k)
  requires (0 <= k < |s| - 1) ==> s[k] <= s[k+1]
  ensures AdjSorted(s)
{
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a    
    ensures AdjSorted(a[..])
    ensures multiset(a[..]) == old(multiset(a[..]))
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant AdjSorted(a[..i])
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant i < a.Length
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant AdjSortedExceptAt(a[..i+1], if j == 0 then -1 else j-1)
      {
        ghost var prePrefix := a[..i+1];
        ghost var preAll := a[..];

        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)

        assert a[..i+1] == Swap(prePrefix, j-1, j);
        assert a[..] == Swap(preAll, j-1, j);

        calc {
          multiset(a[..]);
          == { assert a[..] == Swap(preAll, j-1, j); }
          multiset(Swap(preAll, j-1, j));
          == { MultisetSwapPreserves(preAll, j-1, j); }
          multiset(preAll);
        }

        assert AdjSortedExceptAt(a[..i+1], if j == 1 then -1 else j-2) by {
          SwapMovesInversionLeft(prePrefix, j);
        };

        j := j - 1;

        assert AdjSortedExceptAt(a[..i+1], if j == 0 then -1 else j-1);
      }

      if j > 0 {
        assert a[j-1] <= a[j];
      }

      assert AdjSorted(a[..i+1]) by {
        AdjSortedFromExceptAt(a[..i+1], if j == 0 then -1 else j-1);
      };
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



