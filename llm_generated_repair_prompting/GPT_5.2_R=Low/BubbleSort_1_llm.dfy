/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/



ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost predicate AdjacentSorted(s: seq<int>)
{
  forall i :: 1 <= i < |s| ==> s[i-1] <= s[i]
}

ghost lemma SortedImpliesAdjacent(s: seq<int>)
  ensures Sorted(s) ==> AdjacentSorted(s)
{
}

ghost lemma AdjacentImpliesSorted(s: seq<int>)
  ensures AdjacentSorted(s) ==> Sorted(s)
  decreases |s|
{
  if |s| <= 1 {
  } else {
    assert AdjacentSorted(s[..|s|-1]);
    AdjacentImpliesSorted(s[..|s|-1]);
    assert Sorted(s[..|s|-1]);
    assert forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] by {
      if j < |s|-1 {
      } else {
        if i == |s|-1 {
        } else {
          assert 0 <= i < |s|-1;
          assert Sorted(s[..|s|-1]);
          assert s[i] <= s[|s|-2];
          assert AdjacentSorted(s);
          assert s[|s|-2] <= s[|s|-1];
        }
      }
    };
  }
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant Sorted(a[n..])
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    decreases n
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n
      invariant 0 <= newn <= i
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant forall k, t :: newn <= k < i && 0 <= t < k ==> a[t] <= a[k]
      invariant forall k :: newn < k < i ==> a[k-1] <= a[k]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
      assert a[i-1] <= a[i];
    }

    if newn == 0 {
      assert AdjacentSorted(a[..n]);
      AdjacentImpliesSorted(a[..n]);
      assert Sorted(a[..n]);
      assert forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j];
      assert forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] by {
        if j < n {
          assert Sorted(a[..n]);
        } else if i < n {
        } else {
          assert Sorted(a[n..]);
        }
      };
      return;
    }

    assert forall k :: newn < k < n ==> a[k-1] <= a[k];
    assert forall k, t :: newn <= k < n && 0 <= t < k ==> a[t] <= a[k];

    assert AdjacentSorted(a[newn..n]) by {
      assert forall i2 :: 1 <= i2 < |a[newn..n]| ==> a[newn + i2 - 1] <= a[newn + i2];
    };

    SortedImpliesAdjacent(a[n..]);
    assert AdjacentSorted(a[n..]);

    assert a[n-1] <= a[n] by {
      assert 0 <= n-1 < n <= n < a.Length;
    }

    assert AdjacentSorted(a[newn..]) by {
      assert forall idx :: 1 <= idx < |a[newn..]| ==> a[newn + idx - 1] <= a[newn + idx] by {
        var p := newn + idx;
        if p < n {
          assert newn < p < n;
        } else {
          assert n <= p < a.Length;
          assert AdjacentSorted(a[n..]);
        }
      };
    };
    AdjacentImpliesSorted(a[newn..]);
    assert Sorted(a[newn..]);

    assert forall i0, j0 :: 0 <= i0 < newn <= j0 < a.Length ==> a[i0] <= a[j0] by {
      if j0 < n {
        assert newn <= j0 < n;
        assert 0 <= i0 < j0;
      } else {
        assert 0 <= i0 < n <= j0 < a.Length;
      }
    };

    n := newn;
  }

  if n == 1 {
    assert forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] by {
      if i == 0 {
        assert 0 <= i < n <= j < a.Length;
      } else {
        assert 1 <= i < j < a.Length;
        assert Sorted(a[1..]);
      }
    };
    assert Sorted(a[..]);
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  assert a[..] == [3, 4, 6, 7];
 }
