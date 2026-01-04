/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

// Helper predicate to check if a sequence is sorted
predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if a sequence is sorted up to index n
predicate sortedUpTo(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
{
  forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
}

// Helper predicate to check if the suffix from n is sorted
predicate suffixSorted(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
{
  forall i, j :: n <= i < j < a.Length ==> a[i] <= a[j]
}

// Helper predicate to check if adjacent elements are sorted up to index n
predicate adjacentSorted(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
{
  forall k :: 0 <= k < n-1 ==> a[k] <= a[k+1]
}

// Helper lemma to prove that adjacentSorted implies sortedUpTo
lemma AdjacentSortedImpliesSortedUpTo(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  requires adjacentSorted(a, n)
  ensures sortedUpTo(a, n)
{
  // Transitivity of <= ensures that if all adjacent pairs are sorted,
  // then all pairs are sorted
  forall i, j | 0 <= i < j < n
    ensures a[i] <= a[j]
  {
    var k := i;
    while k < j
      invariant i <= k <= j
      invariant a[i] <= a[k]
    {
      assert a[k] <= a[k+1];
      k := k + 1;
    }
  }
}

// Helper lemma to prove that if suffix is sorted and everything up to n is sorted,
// then the whole array is sorted
lemma CombineSortedParts(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  requires sortedUpTo(a, n)
  requires suffixSorted(a, n)
  ensures sorted(a[..])
{
  // The definition of sorted(a[..]) follows directly from the two predicates
}

// Helper lemma to prove that if adjacentSorted holds for n, then it holds for m < n
lemma AdjacentSortedWeaken(a: array<int>, n: int, m: int)
  requires 0 <= m <= n <= a.Length
  requires adjacentSorted(a, n)
  ensures adjacentSorted(a, m)
{
}

// Helper lemma to prove that if suffixSorted holds for n, then it holds for m > n
lemma SuffixSortedWeaken(a: array<int>, n: int, m: int)
  requires 0 <= n <= m <= a.Length
  requires suffixSorted(a, n)
  ensures suffixSorted(a, m)
{
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var n := a.Length;
  
  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n > 1
    invariant 0 <= n <= a.Length
    invariant suffixSorted(a, n)
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases n
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    
    for i := 1 to n
      invariant 0 <= newn <= i-1
      invariant adjacentSorted(a, newn)
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant newn == 0 || (newn < n && a[newn-1] <= a[newn])
      invariant forall k :: 0 <= k < i-1 ==> a[k] <= a[i-1] || k >= newn
      invariant forall k :: 0 <= k < newn-1 ==> a[k] <= a[k+1]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
    }
    
    // After the inner loop, the largest element in a[..n] is at position n-1
    // and everything from newn to n-1 is sorted
    assert adjacentSorted(a, n);
    // Prove that suffix from newn is sorted
    assert forall i, j :: newn <= i < j < a.Length ==> a[i] <= a[j];
    n := newn;
  }
  
  // When n <= 1, the whole array is sorted
  if n == 1 {
    // Array of length 1 is trivially sorted
    AdjacentSortedImpliesSortedUpTo(a, a.Length);
    CombineSortedParts(a, a.Length);
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  // Add helper assertions to prove the final result
  assert a[..] == [3, 4, 6, 7];
  assert a[0] == 3;
  assert a[1] == 4;
  assert a[2] == 6;
  assert a[3] == 7;
}



