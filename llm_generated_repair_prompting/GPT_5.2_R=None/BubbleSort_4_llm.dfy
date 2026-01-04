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
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant Sorted(a[n..])
    // Cross-boundary property: every element in the (current) prefix is <= every element in the sorted suffix.
    // This is preserved because the inner loop only permutes within a[..n].
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
      // After processing up to i, the segment strictly right of newn (and already scanned)
      // is in nondecreasing order.
      invariant forall p, q :: newn < p < q < i ==> a[p] <= a[q]
      // Everything at/before newn is <= everything strictly to the right of newn (among scanned indices).
      invariant forall x, y :: 0 <= x <= newn < y < i ==> a[x] <= a[y]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
    }

    // From the for-loop invariants at i == n:
    //  - a[newn+1..n) is sorted
    //  - and all elements in a[..newn] are <= all elements in a[newn+1..n)
    n := newn;
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  assert a[..] == [3, 4, 6, 7];
 }
