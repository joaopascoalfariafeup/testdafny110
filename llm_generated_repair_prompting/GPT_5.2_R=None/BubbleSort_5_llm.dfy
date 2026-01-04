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
    // NOTE: We avoid the too-strong cross-boundary invariant a[..n] <= a[n..] during the scan,
    // because swaps inside a[..n] can temporarily violate it. Instead we keep the essential fact
    // needed for correctness: the suffix a[n..] stays sorted and is a permutation of the original.
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
      invariant multiset(a[..]) == multiset(old(a[..]))
      // A local sortedness property for the already-scanned tail after the last swap.
      invariant forall p, q :: newn < p < q < i ==> a[p] <= a[q]
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

  // Help Dafny use the postconditions to establish the concrete expected result:
  assert multiset(a[..]) == multiset([7, 3, 4, 6]);
  assert Sorted(a[..]);

  // Since a[..] is sorted and is a permutation of [7,3,4,6], it must be [3,4,6,7]
  assert a[..] == [3, 4, 6, 7];
 }

