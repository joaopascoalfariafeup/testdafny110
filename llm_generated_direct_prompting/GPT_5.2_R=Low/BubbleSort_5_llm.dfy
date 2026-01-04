/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/



predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method BubbleSort(a: array<int>)
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures Sorted(a[..])
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 1 <= n <= a.Length
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant Sorted(a[n..])
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    decreases n
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;

    var n0 := n;
    for i := 1 to n
      invariant 1 <= n == n0 <= a.Length
      invariant 0 <= newn < n
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant Sorted(a[n..])
      invariant forall x, y :: 0 <= x < n <= y < a.Length ==> a[x] <= a[y]
      invariant forall k :: 0 <= k <= i ==> a[k] <= a[i]
      invariant forall j :: newn < j < i ==> a[j-1] <= a[j]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
      assert forall k :: 0 <= k <= i ==> a[k] <= a[i];
      assert forall j :: newn < j <= i ==> a[j-1] <= a[j];
    }

    assert 0 <= newn < n0;
    assert forall j :: newn < j < n0 ==> a[j-1] <= a[j];

    // The portion a[newn..n0) had no swaps after newn, so it is nondecreasing and
    // every element there is >= any element to its left (otherwise a swap would have occurred later).
    assert forall x, y :: 0 <= x < newn <= y < n0 ==> a[x] <= a[y];

    // Combine with already-sorted suffix a[n0..)
    assert Sorted(a[n0..]);
    assert forall x, y :: 0 <= x < n0 <= y < a.Length ==> a[x] <= a[y];

    n := newn;

    assert Sorted(a[n..n0]);
    assert forall x, y :: 0 <= x < n <= y < n0 ==> a[x] <= a[y];
    assert Sorted(a[n..]);
    assert forall x, y :: 0 <= x < n <= y < a.Length ==> a[x] <= a[y];
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  assert a[..] == [3, 4, 6, 7];
 }
