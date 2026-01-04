/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma SortedEmptyOrSingleton(s: seq<int>)
  ensures |s| <= 1 ==> Sorted(s)
{
}

lemma SortedSuffixExtendByOne(s: seq<int>, k: int)
  requires 0 <= k < |s|
  requires Sorted(s[k+1..])
  requires forall j :: k+1 <= j < |s| ==> s[k] <= s[j]
  ensures Sorted(s[k..])
{
  // Prove directly from the definition of Sorted, by case-splitting on whether one
  // of the indices refers to the newly added head element s[k].
  assert forall i, j :: 0 <= i < j < |s[k..]| ==> s[k..][i] <= s[k..][j] by {
    // Fix: introduce the bound variables explicitly for the proof block
    intro i, j;
    if i == 0 {
      // s[k..][0] is the new head s[k], and j >= 1
      assert 1 <= j;
      assert k + j < |s|;
      assert s[k..][0] == s[k];
      assert s[k..][j] == s[k + j];
      assert s[k] <= s[k + j]; // from the third precondition
    } else {
      // Both indices are in the old suffix s[k+1..]
      assert 1 <= i < j < |s[k..]|;
      assert 0 <= i - 1 < j - 1 < |s[k+1..]|;
      assert s[k..][i] == s[k + i];
      assert s[k..][j] == s[k + j];
      assert s[k+1..][i-1] == s[k+i];
      assert s[k+1..][j-1] == s[k+j];
      // from Sorted(s[k+1..])
      assert s[k+1..][i-1] <= s[k+1..][j-1];
    }
  }
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
    invariant multiset(a[..]) == multiset(old(a[..]))
    // Key strengthening: everything in the prefix is <= everything in the sorted suffix
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
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
      // Maintain cross-boundary ordering throughout the scan
      invariant forall p, q :: 0 <= p < n <= q < a.Length ==> a[p] <= a[q]
      // Strengthening: the element at position i-1 is >= everything to its left (max of a[..i])
      invariant forall p :: 0 <= p < i ==> a[p] <= a[i-1]
      // A local sortedness property for the already-scanned tail after the last swap.
      invariant forall p, q :: newn < p < q < i ==> a[p] <= a[q]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
    }

    // After the scan, position n-1 holds the maximum of a[..n]
    assert forall p :: 0 <= p < n ==> a[p] <= a[n-1];

    // Use that to extend the sorted suffix by one element
    if n < a.Length {
      // show new head a[n-1] is <= every element already in the suffix a[n..]
      assert forall j :: n <= j < a.Length ==> a[n-1] <= a[j] by {
        // from the maintained cross-boundary invariant with p = n-1, q = j
        assert forall p, q :: 0 <= p < n <= q < a.Length ==> a[p] <= a[q];
      }
      SortedSuffixExtendByOne(a[..], n-1);
    } else {
      // suffix is empty; trivially sorted
      SortedEmptyOrSingleton(a[n..]);
    }

    n := newn;
  }

  // When the loop exits, n <= 1. Then a[n..] is sorted and every prefix element is <= every suffix element,
  // which implies the whole array is sorted.
  if n <= 1 {
    if n == 1 {
      // Need to show a[0] <= all elements in a[1..]
      if a.Length > 1 {
        assert forall j :: 1 <= j < a.Length ==> a[0] <= a[j] by {
          // from the outer invariant with i=0, n=1, j
          assert forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j];
        }
        SortedSuffixExtendByOne(a[..], 0);
      } else {
        SortedEmptyOrSingleton(a[..]);
      }
    } else {
      // n==0: a[0..] already sorted by Sorted(a[0..]) = Sorted(a[n..])
      assert a[0..] == a[n..];
    }
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  assert a[..] == [7, 3, 4, 6];
  BubbleSort(a);

  // Help Dafny use the postconditions to establish the concrete expected result:
  assert multiset(a[..]) == multiset([7, 3, 4, 6]);
  assert Sorted(a[..]);

  // Since a[..] is sorted and is a permutation of [7,3,4,6], it must be [3,4,6,7]
  assert a[..] == [3, 4, 6, 7];
}
