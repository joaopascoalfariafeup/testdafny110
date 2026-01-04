/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

// Predicate to check if a sequence is sorted
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Predicate to check if one sequence is a permutation of another
ghost predicate SameMultiset(s1: seq<int>, s2: seq<int>)
{
  multiset(s1) == multiset(s2)
}

// Predicate to check if all elements in s1 are <= all elements in s2
ghost predicate AllLessOrEqual(s1: seq<int>, s2: seq<int>)
{
  forall i, j :: 0 <= i < |s1| && 0 <= j < |s2| ==> s1[i] <= s2[j]
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures SameMultiset(a[..], old(a[..]))
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant Sorted(a[n..])
    invariant AllLessOrEqual(a[..n], a[n..])
    invariant SameMultiset(a[..], old(a[..]))
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 0 <= newn < i <= n
      invariant Sorted(a[n..])
      invariant AllLessOrEqual(a[..n], a[n..])
      invariant SameMultiset(a[..], old(a[..]))
      invariant forall j :: 0 <= j < i ==> a[j] <= a[i-1]
      invariant forall j, k :: newn <= j < k < i ==> a[j] <= a[k]
      invariant newn > 0 ==> forall j :: 0 <= j < newn ==> a[j] <= a[newn]
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
  // BubbleSort guarantees sorted and same multiset, but not specific element positions
  // We can verify the postconditions hold
  assert Sorted(a[..]);
  assert SameMultiset(a[..], [7, 3, 4, 6]);
  // Since sorted and same multiset, the only possibility is [3, 4, 6, 7]
  assert multiset(a[..]) == multiset{3, 4, 6, 7};
  assert |a[..]| == 4;
  assert a[0] in multiset(a[..]);
  assert a[0] >= 3;
  assert a[0] <= a[1] <= a[2] <= a[3];
  assert a[3] in multiset(a[..]);
  assert a[3] <= 7;
  // The sorted sequence with multiset {3,4,6,7} must be [3,4,6,7]
  assert a[..] == [3, 4, 6, 7];
 }

