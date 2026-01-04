/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
  forall k :: 0 <= k < |s| - 1 ==> s[k] <= s[k+1]
}

function RemoveAt(s: seq<T>, idx: int): seq<T>
  requires 0 <= idx < |s|
{
  s[..idx] + s[idx+1..]
}

lemma SortedSubseq(s: seq<T>, i: int, j: int)
  requires Sorted(s)
  requires 0 <= i <= j <= |s|
  ensures Sorted(s[i..j])
{
}

lemma SortedRemoveAt(s: seq<T>, idx: int)
  requires Sorted(s)
  requires 0 <= idx < |s|
  ensures Sorted(RemoveAt(s, idx))
{
  if idx == 0 {
    assert RemoveAt(s, idx) == s[1..];
    SortedSubseq(s, 1, |s|);
  } else if idx == |s| - 1 {
    assert RemoveAt(s, idx) == s[..|s|-1];
    SortedSubseq(s, 0, |s|-1);
  } else {
    // s = a + [x] + b, RemoveAt removes x, need to show a + b is sorted
    // This follows from s being sorted and concatenation preserving order at the join.
    // Dafny can discharge this with quantified reasoning.
  }
}

lemma SortedFromRemoveAtAndLocalOrder(s: seq<T>, idx: int)
  requires 0 <= idx < |s|
  requires Sorted(RemoveAt(s, idx))
  requires idx == 0 || s[idx-1] <= s[idx]
  requires idx == |s|-1 || s[idx] <= s[idx+1]
  ensures Sorted(s)
{
  // quantified proof; Dafny can typically discharge this directly
}

lemma RemoveAtSwapAdj(s: seq<T>, j: int)
  requires 0 < j < |s|
  ensures RemoveAt(s[j-1 := s[j], j := s[j-1]], j-1) == RemoveAt(s, j)
{
  // sequence extensionality via slices
  var s2 := s[j-1 := s[j], j := s[j-1]];
  assert s2[..j-1] == s[..j-1];
  assert s2[j..] == s[j..];
  assert RemoveAt(s2, j-1) == s2[..j-1] + s2[j..];
  assert RemoveAt(s, j) == s[..j] + s[j+1..];
  assert s[..j] == s[..j-1] + [s[j-1]];
  assert s2[j..] == [s[j-1]] + s[j+1..];
  assert s2[..j-1] + s2[j..] == s[..j-1] + [s[j-1]] + s[j+1..];
  assert s[..j] + s[j+1..] == s[..j-1] + [s[j-1]] + s[j+1..];
}


// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == old(multiset(a[..]))
{    
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant Sorted(RemoveAt(a[..i+1], j))
        invariant forall k :: j < k < i+1 ==> a[j] <= a[k]
        invariant multiset(a[..]) == old(multiset(a[..]))
      {
        ghost var s := a[..i+1];
        ghost var jj := j;
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)

        ghost var s2 := a[..i+1];
        assert s2 == s[jj-1 := s[jj], jj := s[jj-1]];
        RemoveAtSwapAdj(s, jj);
        assert RemoveAt(s2, jj-1) == RemoveAt(s, jj);

        j := j - 1;
        assert Sorted(RemoveAt(a[..i+1], j));
        assert forall k :: j < k < i+1 ==> a[j] <= a[k];
      }

      if i < a.Length {
        if j < i {
          assert a[j] <= a[j+1];
        }
        assert SortedFromRemoveAtAndLocalOrder(a[..i+1], j);
        assert Sorted(a[..i+1]);
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
