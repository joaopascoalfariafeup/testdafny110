/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

// Ghost function to check if a sequence is sorted
ghost function IsSorted(s: seq<int>): bool
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures forall i :: 0 <= i < a.Length ==> old(a).Contains(a[i])
  ensures forall i :: 0 <= i < old(a.Length) ==> a.Contains(old(a)[i])
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 1 <= n <= a.Length
    invariant IsSorted(a[n..])
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant forall i :: 0 <= i < a.Length ==> old(a).Contains(a[i])
    invariant forall i :: 0 <= i < old(a.Length) ==> a.Contains(old(a)[i])
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n+1
      invariant forall j :: 0 <= j < i-1 ==> a[j] <= a[j+1]
      invariant forall j :: 0 <= j < i ==> a[j] <= a[i-1]
      invariant forall j :: i < j < n ==> a[i-1] <= a[j]
      invariant newn == 0 || (newn < i && a[newn-1] > a[newn])
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
