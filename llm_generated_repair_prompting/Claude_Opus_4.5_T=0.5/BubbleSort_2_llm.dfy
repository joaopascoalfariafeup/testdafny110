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

// Lemma: Two sorted sequences with the same multiset are equal
lemma SortedPermutationUnique(s1: seq<int>, s2: seq<int>)
  requires Sorted(s1)
  requires Sorted(s2)
  requires multiset(s1) == multiset(s2)
  ensures s1 == s2
{
  if |s1| == 0 {
    assert |s2| == 0;
  } else {
    assert s1[0] in multiset(s1);
    assert s1[0] in multiset(s2);
    assert s1[0] in s2;
    
    assert s2[0] in multiset(s2);
    assert s2[0] in multiset(s1);
    assert s2[0] in s1;
    
    // Both s1[0] and s2[0] are minimums of their respective sequences
    assert forall i :: 0 <= i < |s1| ==> s1[0] <= s1[i];
    assert forall i :: 0 <= i < |s2| ==> s2[0] <= s2[i];
    
    // Since s1[0] is in s2 and s2[0] is minimum of s2, s2[0] <= s1[0]
    // Since s2[0] is in s1 and s1[0] is minimum of s1, s1[0] <= s2[0]
    assert s1[0] == s2[0];
    
    assert multiset(s1[1..]) == multiset(s1) - multiset{s1[0]};
    assert multiset(s2[1..]) == multiset(s2) - multiset{s2[0]};
    assert multiset(s1[1..]) == multiset(s2[1..]);
    
    SortedPermutationUnique(s1[1..], s2[1..]);
    assert s1[1..] == s2[1..];
    assert s1 == [s1[0]] + s1[1..];
    assert s2 == [s2[0]] + s2[1..];
  }
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
      invariant 0 <= newn < i
      invariant forall j, k :: newn <= j < k < i ==> a[j] <= a[k]
      invariant forall j :: newn <= j < i ==> forall k :: 0 <= k < j ==> a[k] <= a[j]
      invariant Sorted(a[n..])
      invariant AllLessOrEqual(a[..n], a[n..])
      invariant SameMultiset(a[..], old(a[..]))
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
  assert a[..] == [7, 3, 4, 6];
  BubbleSort(a);
  assert Sorted(a[..]);
  assert multiset(a[..]) == multiset([7, 3, 4, 6]);
  assert Sorted([3, 4, 6, 7]);
  assert multiset([3, 4, 6, 7]) == multiset([7, 3, 4, 6]);
  SortedPermutationUnique(a[..], [3, 4, 6, 7]);
  assert a[..] == [3, 4, 6, 7];
 }
