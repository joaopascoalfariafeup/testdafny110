/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

// Auxiliary ghost function to check if a sequence is sorted in increasing order.
ghost function IsSorted(s: seq<int>): bool
{
  forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i+1]
}

// Auxiliary ghost function to check if two sequences are permutations of each other.
ghost function IsPermutation(s: seq<int>, t: seq<int>): bool
{
  forall x :: (count x in s) == (count x in t)
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  requires a != null
  ensures old(a.Length) == a.Length
  ensures IsSorted(a[..])
  ensures IsPermutation(old(a[..]), a[..])
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 1 <= n <= a.Length
    invariant IsSorted(a[n..])
    invariant IsPermutation(old(a[..]), a[..])
    decreases n
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n+1
      invariant forall k :: 0 <= k < i-1 ==> a[k] <= a[k+1]
      invariant forall k :: 0 <= k < i-1 ==> a[k] <= a[n-1]
      invariant IsPermutation(old(a[..]), a[..])
      decreases n-i
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
