
/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

// Checks if array segment a[lo..hi] is sorted in ascending order
ghost predicate Sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

// Checks if sequence s is sorted in ascending order
ghost predicate SortedSeq(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Checks if all elements in a[lo..hi] are <= all elements in a[hi..end]
ghost predicate Partitioned(a: array<int>, lo: int, hi: int, end: int)
  reads a
  requires 0 <= lo <= hi <= end <= a.Length
{
  forall i, j :: lo <= i < hi <= j < end ==> a[i] <= a[j]
}

// Checks if sequence s1 is a permutation of sequence s2
ghost predicate IsPermutation(s1: seq<int>, s2: seq<int>)
{
  multiset(s1) == multiset(s2)
}

// Lemma: Two sorted sequences that are permutations of each other must be equal
lemma SortedPermutationUnique(s1: seq<int>, s2: seq<int>)
  requires SortedSeq(s1)
  requires SortedSeq(s2)
  requires IsPermutation(s1, s2)
  ensures s1 == s2
{
  if |s1| == 0 {
  } else {
    var m1 := multiset(s1);
    var m2 := multiset(s2);
    assert m1 == m2;
    assert s1[0] in m1;
    assert s1[0] in m2;
    assert s1[0] in s2;
    
    // The minimum element must be at position 0 in both sorted sequences
    assert forall i :: 0 <= i < |s1| ==> s1[0] <= s1[i];
    assert forall i :: 0 <= i < |s2| ==> s2[0] <= s2[i];
    
    // Since they have the same multiset, they have the same minimum
    assert s1[0] == s2[0];
    
    // Recurse on the tails
    SortedPermutationUnique(s1[1..], s2[1..]);
  }
}

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a, 0, a.Length)
  ensures SortedSeq(a[..])
  ensures IsPermutation(a[..], old(a[..]))
{
    // In each iteration, find the minimum value in the unsorted part of the array
    // (on the right) and append it (by swapping) to the sorted part (on the left).
    for i := 0 to a.Length 
      invariant Sorted(a, 0, i)
      invariant Partitioned(a, 0, i, a.Length)
      invariant IsPermutation(a[..], old(a[..]))
    {
        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i <= jMin < j
          invariant forall k :: i <= k < j ==> a[jMin] <= a[k]
        {
            if a[j] < a[jMin] {
                jMin := j;
            }
        } 
        // Swap it with the first unsorted element
        if jMin != i {
          a[i], a[jMin] := a[jMin], a[i]; 
        }
    }
}


// Test case checked statically.
method {:fuel IsPermutation, 5} testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  assert a[..] == [9, 4, 6, 1, 8];
  SelectionSort(a);
  
  // The expected result
  var expected := [1, 4, 6, 8, 9];
  
  // Prove that expected is sorted
  assert SortedSeq(expected);
  
  // Prove that expected is a permutation of the original
  assert multiset([9, 4, 6, 1, 8]) == multiset([1, 4, 6, 8, 9]);
  assert IsPermutation(expected, [9, 4, 6, 1, 8]);
  
  // Use the lemma to conclude equality
  SortedPermutationUnique(a[..], expected);
  
  assert a[..] == [1, 4, 6, 8, 9];
}
