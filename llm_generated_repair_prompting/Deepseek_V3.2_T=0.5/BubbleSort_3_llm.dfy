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
  requires a != null
  requires 0 <= n <= a.Length
  reads a
{
  forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
}

// Helper predicate to check if the suffix from n is sorted
predicate suffixSorted(a: array<int>, n: int)
  requires a != null
  requires 0 <= n <= a.Length
  reads a
{
  forall i, j :: n <= i < j < a.Length ==> a[i] <= a[j]
}

// Helper predicate to check if adjacent elements are sorted up to index n
predicate adjacentSorted(a: array<int>, n: int)
  requires a != null
  requires 0 <= n <= a.Length
  reads a
{
  forall k :: 0 <= k < n-1 ==> a[k] <= a[k+1]
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  requires a != null
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
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
    }
    
    // After the inner loop, the largest element in a[..n] is at position n-1
    // and everything from newn to n-1 is sorted
    assert adjacentSorted(a, n);
    n := newn;
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  assert a[..] == [3, 4, 6, 7];
}

