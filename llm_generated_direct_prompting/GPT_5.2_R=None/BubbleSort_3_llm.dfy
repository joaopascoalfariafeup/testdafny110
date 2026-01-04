/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/



ghost predicate SortedRange(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  reads a
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

ghost predicate PartitionLe(a: array<int>, lo1: int, hi1: int, lo2: int, hi2: int)
  requires 0 <= lo1 <= hi1 <= a.Length
  requires 0 <= lo2 <= hi2 <= a.Length
  reads a
{
  forall i, j :: lo1 <= i < hi1 && lo2 <= j < hi2 ==> a[i] <= a[j]
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures SortedRange(a, 0, a.Length)
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant SortedRange(a, n, a.Length)
    invariant PartitionLe(a, 0, n, n, a.Length)
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 0 <= newn < n
      invariant SortedRange(a, n, a.Length)
      invariant PartitionLe(a, 0, n, n, a.Length)
      invariant forall k :: 0 <= k < i ==> a[k] <= a[i-1]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
    }
    n := newn;
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  assert a[..] == [3, 4, 6, 7];
 }
