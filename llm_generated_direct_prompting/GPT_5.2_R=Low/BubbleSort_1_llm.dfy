/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/



ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma SeqContainsIndex(s: seq<int>, v: int)
  requires v in s
  ensures exists i :: 0 <= i < |s| && s[i] == v
{
}

lemma SortedMultisetUnique_3467(s: seq<int>)
  requires Sorted(s)
  requires |s| == 4
  requires multiset(s) == multiset([3, 4, 6, 7])
  ensures s == [3, 4, 6, 7]
{
  assert 3 in s;
  assert 4 in s;
  assert 6 in s;
  assert 7 in s;

  SeqContainsIndex(s, 3);
  SeqContainsIndex(s, 4);
  SeqContainsIndex(s, 6);
  SeqContainsIndex(s, 7);

  var i3 :| 0 <= i3 < |s| && s[i3] == 3;
  var i4 :| 0 <= i4 < |s| && s[i4] == 4;
  var i6 :| 0 <= i6 < |s| && s[i6] == 6;
  var i7 :| 0 <= i7 < |s| && s[i7] == 7;

  assert s[0] in multiset(s);
  assert s[0] in multiset([3, 4, 6, 7]);
  assert s[0] == 3 || s[0] == 4 || s[0] == 6 || s[0] == 7;

  assert s[0] <= s[i3];
  assert s[0] <= 3;
  assert s[0] == 3;

  assert i4 != 0;
  assert i4 >= 1;

  assert s[1] in multiset(s);
  assert s[1] in multiset([3, 4, 6, 7]);
  assert s[1] == 3 || s[1] == 4 || s[1] == 6 || s[1] == 7;

  assert s[1] <= s[i4];
  assert s[1] <= 4;
  assert s[1] != 3;
  assert s[1] == 4;

  assert i6 != 0 && i6 != 1;
  assert i6 >= 2;

  assert s[2] in multiset(s);
  assert s[2] in multiset([3, 4, 6, 7]);
  assert s[2] == 3 || s[2] == 4 || s[2] == 6 || s[2] == 7;

  assert s[2] <= s[i6];
  assert s[2] <= 6;
  assert s[2] != 3 && s[2] != 4;
  assert s[2] == 6;

  assert s[3] in multiset(s);
  assert s[3] in multiset([3, 4, 6, 7]);
  assert s[3] == 3 || s[3] == 4 || s[3] == 6 || s[3] == 7;
  assert s[3] != 3 && s[3] != 4 && s[3] != 6;
  assert s[3] == 7;
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
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases n
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n
      invariant 0 <= newn < i
      invariant n <= a.Length
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k :: 0 <= k < i ==> a[k] <= a[i-1]
      invariant forall k :: newn < k < i ==> a[k-1] <= a[k]
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
  assert multiset(a[..]) == multiset([3, 4, 6, 7]);
  SortedMultisetUnique_3467(a[..]);
  assert a[..] == [3, 4, 6, 7];
 }
