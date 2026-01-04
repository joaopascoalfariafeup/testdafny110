/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/



ghost predicate AdjSorted(s: seq<int>)
{
  forall k :: 0 <= k < |s| - 1 ==> s[k] <= s[k + 1]
}

ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma AdjSortedImpliesSorted(s: seq<int>)
  requires AdjSorted(s)
  ensures Sorted(s)
{
  forall i, j | 0 <= i < j < |s|
    ensures s[i] <= s[j]
  {
    var k := i;
    while k < j
      invariant i <= k <= j
      invariant (forall t :: i <= t < k ==> s[i] <= s[t])
      decreases j - k
    {
      if k == i {
        assert s[i] <= s[i];
      } else {
        assert s[i] <= s[k];
      }
      assert 0 <= k < |s| - 1;
      assert s[k] <= s[k + 1];
      if k == i {
        assert s[i] <= s[k + 1];
      } else {
        assert s[i] <= s[k];
        assert s[k] <= s[k + 1];
        assert s[i] <= s[k + 1];
      }
      k := k + 1;
    }
    assert s[i] <= s[j];
  }
}

lemma IdentifySortedBubbleTestResult(s: seq<int>)
  requires |s| == 4
  requires AdjSorted(s)
  requires multiset(s) == multiset([7, 3, 4, 6])
  ensures s == [3, 4, 6, 7]
{
  AdjSortedImpliesSorted(s);
  assert multiset([7, 3, 4, 6])[3] == 1;
  assert multiset([7, 3, 4, 6])[4] == 1;
  assert multiset([7, 3, 4, 6])[6] == 1;
  assert multiset([7, 3, 4, 6])[7] == 1;

  assert multiset(s)[3] == 1;
  assert multiset(s)[4] == 1;
  assert multiset(s)[6] == 1;
  assert multiset(s)[7] == 1;

  assert 3 in multiset(s);
  assert 7 in multiset(s);

  // s[0] is the minimum element
  assert forall i :: 0 <= i < |s| ==> s[0] <= s[i];
  if s[0] != 3 {
    assert s[0] == 4 || s[0] == 6 || s[0] == 7;
    assert s[0] > 3;
    assert forall i :: 0 <= i < |s| ==> 3 < s[i];
    assert multiset(s)[3] == 0;
    assert false;
  }
  assert s[0] == 3;

  // s[3] is the maximum element
  assert forall i :: 0 <= i < |s| ==> s[i] <= s[|s| - 1];
  if s[|s| - 1] != 7 {
    assert s[|s| - 1] == 3 || s[|s| - 1] == 4 || s[|s| - 1] == 6;
    assert s[|s| - 1] < 7;
    assert forall i :: 0 <= i < |s| ==> s[i] < 7;
    assert multiset(s)[7] == 0;
    assert false;
  }
  assert s[3] == 7;

  // Middle elements must be 4 and 6, and sorted order fixes them
  assert s[1] == 4 || s[1] == 6;
  assert s[2] == 4 || s[2] == 6;
  assert s[1] <= s[2];
  assert s[1] == 4;
  assert s[2] == 6;

  assert s == [3, 4, 6, 7];
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures a.Length == old(a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures AdjSorted(a[..])
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: n <= k < a.Length - 1 ==> a[k] <= a[k + 1]
    invariant n <= 1 ==> (a.Length <= 1 || a[0] <= a[1])
    decreases n
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n
      invariant 0 <= newn <= i - 1
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k :: n <= k < a.Length - 1 ==> a[k] <= a[k + 1]
      invariant forall k :: newn < k < i ==> a[k - 1] <= a[k]
      invariant newn == 1 ==> a[0] <= a[1]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
        assert newn == i;
        if newn == 1 {
          assert a[0] <= a[1];
        }
      } else {
        assert a[i - 1] <= a[i];
      }
      if newn < i {
        assert a[i - 1] <= a[i];
      }
    }
    if newn == 0 {
      assert forall k :: 0 < k < n ==> a[k - 1] <= a[k];
    } else {
      assert forall k :: newn < k < n ==> a[k - 1] <= a[k];
      assert newn == 1 ==> a[0] <= a[1];
    }
    n := newn;
  }

  if n == 0 {
    assert forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k + 1];
  } else if n == 1 {
    if a.Length > 1 {
      assert a[0] <= a[1];
      assert forall k :: 1 <= k < a.Length - 1 ==> a[k] <= a[k + 1];
    }
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  IdentifySortedBubbleTestResult(a[..]);
  assert a[..] == [3, 4, 6, 7];
 }
