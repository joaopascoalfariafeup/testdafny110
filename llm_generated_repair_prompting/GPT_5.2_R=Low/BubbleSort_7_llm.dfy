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

lemma SortedImpliesAdjacent(s: seq<int>)
  ensures Sorted(s) ==> AdjacentSorted(s)
{
  if Sorted(s) {
    assert forall i :: 1 <= i < |s| ==> s[i-1] <= s[i] by {
      assert 0 <= i-1 < i < |s|;
    };
  }
}

lemma AdjacentLeq(s: seq<int>, i: int, j: int)
  requires AdjacentSorted(s)
  requires 0 <= i < j < |s|
  ensures s[i] <= s[j]
  decreases j - i
{
  if j == i + 1 {
    assert 1 <= j < |s|;
    assert s[j-1] <= s[j];
  } else {
    AdjacentLeq(s, i, j - 1);
    assert 1 <= j < |s|;
    assert s[j-1] <= s[j];
  }
}

lemma AdjacentImpliesSorted(s: seq<int>)
  ensures AdjacentSorted(s) ==> Sorted(s)
{
  if AdjacentSorted(s) {
    assert forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] by {
      AdjacentLeq(s, i, j);
    };
  }
}

lemma SliceIndex(a: array<int>, lo: int, hi: int, k: int)
  requires a != null
  requires 0 <= lo <= hi <= a.Length
  requires 0 <= k < hi - lo
  ensures (a[lo..hi])[k] == a[lo + k]
{
}

method BubbleSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  while n > 1
    invariant 0 <= n <= a.Length
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant Sorted(a[n..])
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    decreases n
  {
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
      assert AdjacentSorted(a[..n]) by {
        assert forall k :: 1 <= k < |a[..n]| ==> (a[..n])[k-1] <= (a[..n])[k] by {
          assert |a[..n]| == n;
          assert 1 <= k < n;
          assert a[k-1] <= a[k];
        };
      };
      AdjacentImpliesSorted(a[..n]);
      assert Sorted(a[..n]);

      // Entire array is sorted: prefix sorted, suffix sorted (loop invariant), and cross-order (loop invariant)
      assert Sorted(a[..]) by {
        assert forall ii, jj :: 0 <= ii < jj < a.Length ==> a[ii] <= a[jj] by {
          if jj < n {
            // both in the prefix
            assert 0 <= ii < jj < n;
            SliceIndex(a, 0, n, ii);
            SliceIndex(a, 0, n, jj);
            assert (a[..n])[ii] <= (a[..n])[jj];
          } else if ii < n {
            // crossing boundary, use loop invariant
            assert 0 <= ii < n <= jj < a.Length;
          } else {
            // both in the suffix
            assert n <= ii < jj < a.Length;
            var si := ii - n;
            var sj := jj - n;
            assert 0 <= si < sj < |a[n..]|;
            SliceIndex(a, n, a.Length, si);
            SliceIndex(a, n, a.Length, sj);
            assert (a[n..])[si] <= (a[n..])[sj];
          }
        };
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

    if n < a.Length {
      assert a[n-1] <= a[n] by {
        assert 0 <= n-1 < n <= n < a.Length;
      }
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

method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  assert a[..] == [3, 4, 6, 7];
}
