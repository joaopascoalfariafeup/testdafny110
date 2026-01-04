/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

// Checks if a sequence is sorted in ascending order
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Checks if sequence s is a permutation of sequence t
ghost predicate IsPermutation(s: seq<int>, t: seq<int>)
{
  multiset(s) == multiset(t)
}

// Checks if all elements in s1 are less than or equal to all elements in s2
ghost predicate AllLessOrEqual(s1: seq<int>, s2: seq<int>)
{
  forall i, j :: 0 <= i < |s1| && 0 <= j < |s2| ==> s1[i] <= s2[j]
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures IsPermutation(a[..], old(a[..]))
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant Sorted(a[n..])
    invariant AllLessOrEqual(a[..n], a[n..])
    invariant IsPermutation(a[..], old(a[..]))
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 0 <= newn < i <= n
      invariant forall j, k :: 0 <= j < k <= newn ==> a[j] <= a[k]
      invariant forall j :: newn < j < i ==> a[j-1] <= a[j]
      invariant forall j :: 0 <= j < i ==> a[j] <= a[i-1]
      invariant Sorted(a[n..])
      invariant AllLessOrEqual(a[..n], a[n..])
      invariant IsPermutation(a[..], old(a[..]))
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
