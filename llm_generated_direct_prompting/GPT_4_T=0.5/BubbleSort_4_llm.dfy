/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

// Auxiliary function to check if a sequence is sorted
function IsSorted(s: seq<int>): bool
{
  forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i+1]
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures old(IsSorted(a[..])) ==> IsSorted(a[..]) // if the array was sorted, it remains sorted
  ensures forall k :: 0 <= k < a.Length ==> old(Count(a[..], a[k])) == Count(a[..], a[k]) // the number of occurrences of each element remains the same
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 1 <= n <= a.Length
    invariant IsSorted(a[n..])
    invariant forall k :: n <= k < a.Length ==> forall j :: 0 <= j < n ==> a[j] <= a[k] // elements in a[n..] are greater or equal than elements in a[..n]
    invariant forall k :: 0 <= k < a.Length ==> old(Count(a[..], a[k])) == Count(a[..], a[k]) // the number of occurrences of each element remains the same
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n
      invariant forall k :: 0 <= k < i ==> a[k] <= a[i] // elements in a[..i] are less or equal than a[i]
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
