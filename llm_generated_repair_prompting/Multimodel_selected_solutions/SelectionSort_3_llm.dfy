/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

// Checks if array segment a[lo..hi] is sorted
ghost predicate Sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

// Checks if sequence is sorted
ghost predicate SortedSeq(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Checks if all elements in a[lo..hi] are >= all elements in a[lo2..hi2]
ghost predicate Partitioned(a: array<int>, lo: int, hi: int, lo2: int, hi2: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
  requires 0 <= lo2 <= hi2 <= a.Length
{
  forall i, j :: lo <= i < hi && lo2 <= j < hi2 ==> a[i] <= a[j]
}

// Checks if two sequences are permutations of each other
ghost predicate IsPermutation(s1: seq<int>, s2: seq<int>)
{
  multiset(s1) == multiset(s2)
}

// Helper lemma: multiset of tail equals multiset minus head
lemma MultisetTail<T>(s: seq<T>)
  requires |s| > 0
  ensures multiset(s[1..]) == multiset(s) - multiset{s[0]}
{
  assert s == [s[0]] + s[1..];
  assert multiset(s) == multiset{s[0]} + multiset(s[1..]);
}

// Lemma: Two sorted sequences that are permutations of each other are equal
lemma SortedPermutationUnique(s1: seq<int>, s2: seq<int>)
  requires SortedSeq(s1)
  requires SortedSeq(s2)
  requires IsPermutation(s1, s2)
  ensures s1 == s2
{
  if |s1| == 0 {
    assert |s2| == 0;
  } else {
    assert s1[0] in multiset(s1);
    assert s1[0] in multiset(s2);
    assert s2[0] in multiset(s2);
    assert s2[0] in multiset(s1);
    // Both s1[0] and s2[0] are minimums of their respective sequences
    // Since they have the same multiset, they must be equal
    assert forall i :: 0 <= i < |s1| ==> s1[0] <= s1[i];
    assert forall i :: 0 <= i < |s2| ==> s2[0] <= s2[i];
    // s1[0] is in s2, so s2[0] <= s1[0]
    // s2[0] is in s1, so s1[0] <= s2[0]
    // Therefore s1[0] == s2[0]
    assert s1[0] == s2[0];
    MultisetTail(s1);
    MultisetTail(s2);
    assert multiset(s1[1..]) == multiset(s1) - multiset{s1[0]};
    assert multiset(s2[1..]) == multiset(s2) - multiset{s2[0]};
    assert IsPermutation(s1[1..], s2[1..]);
    SortedPermutationUnique(s1[1..], s2[1..]);
  }
}

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a, 0, a.Length)
  ensures IsPermutation(a[..], old(a[..]))
{
    // In each iteration, find the minimum value in the unsorted part of the array
    // (on the right) and append it (by swapping) to the sorted part (on the left).
    for i := 0 to a.Length 
      invariant Sorted(a, 0, i)
      invariant Partitioned(a, 0, i, i, a.Length)
      invariant IsPermutation(a[..], old(a[..]))
    {
        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i <= jMin < a.Length
          invariant i + 1 <= j <= a.Length
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
method testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  assert a[..] == [9, 4, 6, 1, 8];
  SelectionSort(a);
  // The result is sorted and a permutation of the original
  assert Sorted(a, 0, a.Length);
  assert SortedSeq(a[..]);
  assert IsPermutation(a[..], [9, 4, 6, 1, 8]);
  // [1, 4, 6, 8, 9] is sorted and a permutation of [9, 4, 6, 1, 8]
  assert SortedSeq([1, 4, 6, 8, 9]);
  assert IsPermutation([1, 4, 6, 8, 9], [9, 4, 6, 1, 8]);
  // By uniqueness lemma, they must be equal
  SortedPermutationUnique(a[..], [1, 4, 6, 8, 9]);
  assert a[..] == [1, 4, 6, 8, 9];
}

