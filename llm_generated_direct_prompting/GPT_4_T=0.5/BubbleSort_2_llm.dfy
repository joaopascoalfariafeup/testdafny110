/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

ghost function IsSorted(a: array<int>, n: nat): bool
{
  forall k :: 0 <= k < n - 1 ==> a[k] <= a[k+1]
}

ghost function IsPermutation(a: array<int>, b: array<int>): bool
{
  forall i :: 0 <= i < a.Length ==> 
    (exists j :: 0 <= j < b.Length && a[i] == b[j]) &&
  forall j :: 0 <= j < b.Length ==> 
    (exists i :: 0 <= i < a.Length && a[i] == b[j])
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  requires a.Length > 0
  ensures IsSorted(a, a.Length)
  ensures IsPermutation(a, old(a))
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 1 <= n <= a.Length
    invariant IsSorted(a, a.Length - n + 1)
    invariant IsPermutation(a, old(a))
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n+1
      invariant forall k :: 0 <= k < i-1 ==> a[k] <= a[k+1]
      invariant forall k :: i-1 < k < n ==> a[i-1] <= a[k]
      invariant newn == 0 || (newn < i && a[newn-1] <= a[newn])
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
