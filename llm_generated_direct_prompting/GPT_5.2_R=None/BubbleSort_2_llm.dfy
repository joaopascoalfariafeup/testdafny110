/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/



ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate MultisetEq(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}


// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures MultisetEq(a[..], old(a[..]))
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant Sorted(a[n..])
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    invariant MultisetEq(a[..], old(a[..]))
    decreases n
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n
      invariant 0 <= newn < i
      invariant MultisetEq(a[..], old(a[..]))
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
