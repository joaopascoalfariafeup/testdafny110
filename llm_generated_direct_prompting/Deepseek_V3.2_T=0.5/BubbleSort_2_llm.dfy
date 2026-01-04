/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/



// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant forall i, j :: n <= i < j < a.Length ==> a[i] <= a[j]
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j] || exists k :: 0 <= k < n-1 && a[k] > a[k+1]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 0 <= newn <= i-1
      invariant forall k :: 0 <= k < i-1 && k+1 < n ==> a[k] <= a[k+1] || exists l :: 0 <= l < i-1 && a[l] > a[l+1]
      invariant multiset(a[..]) == multiset(old(a[..]))
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
