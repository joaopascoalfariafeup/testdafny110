/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  // array<T> is already non-null, so no need for a != null
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant Sorted(a[n..])
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases n
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= n <= a.Length
      invariant 1 <= i <= n
      invariant 0 <= newn < i
      invariant Sorted(a[n..])
      invariant forall x, y :: 0 <= x < n <= y < a.Length ==> a[x] <= a[y]
      invariant multiset(a[..]) == multiset(old(a[..]))
      // Key facts for proving the outer-loop invariants after setting n := newn:
      //  (1) everything strictly to the right of newn is already in nondecreasing order
      invariant forall p, q :: newn < p < q < n ==> a[p] <= a[q]
      //  (2) and everything at/before newn is <= everything strictly to the right of newn
      invariant forall x, y :: 0 <= x <= newn < y < n ==> a[x] <= a[y]
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

