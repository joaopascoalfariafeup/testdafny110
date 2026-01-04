/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/



predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma SortedSingleton(s: seq<int>)
  ensures |s| <= 1 ==> Sorted(s)
{
}

lemma SortedConcat(s: seq<int>, t: seq<int>)
  requires Sorted(s)
  requires Sorted(t)
  requires forall i, j :: 0 <= i < |s| && 0 <= j < |t| ==> s[i] <= t[j]
  ensures Sorted(s + t)
{
  assert forall i, j :: 0 <= i < j < |s + t| ==> (s + t)[i] <= (s + t)[j] by {
    assume i, j | 0 <= i < j < |s + t|;
    if j < |s| {
      assert (s + t)[i] == s[i];
      assert (s + t)[j] == s[j];
      assert s[i] <= s[j];
    } else if i < |s| {
      assert (s + t)[i] == s[i];
      assert (s + t)[j] == t[j - |s|];
      assert s[i] <= t[j - |s|];
    } else {
      assert (s + t)[i] == t[i - |s|];
      assert (s + t)[j] == t[j - |s|];
      assert t[i - |s|] <= t[j - |s|];
    }
  }
}

lemma SortedUnique(s: seq<int>, t: seq<int>)
  requires Sorted(s)
  requires Sorted(t)
  requires multiset(s) == multiset(t)
  ensures s == t
  decreases |s|
{
  if |s| == 0 {
    assert |t| == 0;
  } else {
    assert |t| == |s|;
    // show s[0] == t[0]
    assert s[0] <= t[0] by {
      if t[0] < s[0] {
        assert t[0] in multiset(t);
        assert t[0] in multiset(s);
        var k : int :| 0 <= k < |s| && s[k] == t[0];
        assert s[0] <= s[k];
        assert s[k] == t[0];
        assert false;
      }
    }
    assert t[0] <= s[0] by {
      if s[0] < t[0] {
        assert s[0] in multiset(s);
        assert s[0] in multiset(t);
        var k : int :| 0 <= k < |t| && t[k] == s[0];
        assert t[0] <= t[k];
        assert t[k] == s[0];
        assert false;
      }
    }
    assert s[0] == t[0];

    // tails have same multiset
    assert multiset(s[1..])[s[0]] + 1 == multiset(s)[s[0]];
    assert multiset(t[1..])[t[0]] + 1 == multiset(t)[t[0]];
    assert forall x :: multiset(s[1..])[x] == multiset(t[1..])[x] by {
      assume x;
      if x == s[0] {
        assert multiset(s)[x] == multiset(t)[x];
        assert multiset(s)[x] == multiset(s[1..])[x] + 1;
        assert multiset(t)[x] == multiset(t[1..])[x] + 1;
      } else {
        assert multiset(s)[x] == multiset(t)[x];
        assert multiset(s)[x] == multiset(s[1..])[x];
        assert multiset(t)[x] == multiset(t[1..])[x];
      }
    }
    assert multiset(s[1..]) == multiset(t[1..]);

    SortedUnique(s[1..], t[1..]);
    assert s == t;
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
    invariant Sorted(a[n..])
    invariant forall p, q :: 0 <= p < n && n <= q < a.Length ==> a[p] <= a[q]
    invariant multiset(a[..]) == old(multiset(a[..]))
    decreases n
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n
      invariant 0 <= newn < i
      invariant Sorted(a[n..])
      invariant forall p, q :: 0 <= p < n && n <= q < a.Length ==> a[p] <= a[q]
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant forall p, q :: 0 <= p < q < i ==> q < newn || a[p] <= a[q]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
    }

    // establish next-iteration invariants for n := newn
    assert Sorted(a[newn..n]) by {
      assert forall p, q :: 0 <= p < q < n - newn ==> (a[newn..n])[p] <= (a[newn..n])[q] by {
        assume p, q | 0 <= p < q < n - newn;
        assert newn + p < newn + q < n;
        assert forall x, y :: 0 <= x < y < n ==> y < newn || a[x] <= a[y] by { }
        assert (newn + q) < newn || a[newn + p] <= a[newn + q];
        assert a[newn + p] <= a[newn + q];
        assert (a[newn..n])[p] == a[newn + p];
        assert (a[newn..n])[q] == a[newn + q];
      }
    }
    assert forall p, q :: 0 <= p < newn && newn <= q < n ==> a[p] <= a[q] by {
      assume p, q | 0 <= p < newn && newn <= q < n;
      if q < newn {
        assert false;
      } else {
        // from inner-loop invariant at i==n
        assert forall x, y :: 0 <= x < y < n ==> y < newn || a[x] <= a[y];
        assert a[p] <= a[q];
      }
    }
    assert forall p, q :: 0 <= p < newn && n <= q < a.Length ==> a[p] <= a[q] by {
      assume p, q | 0 <= p < newn && n <= q < a.Length;
      assert 0 <= p < n;
      assert a[p] <= a[q];
    }
    assert forall p, q :: newn <= p < n && n <= q < a.Length ==> a[p] <= a[q] by {
      assume p, q | newn <= p < n && n <= q < a.Length;
      assert 0 <= p < n;
      assert a[p] <= a[q];
    }
    assert Sorted(a[newn..]) by {
      // a[newn..] == a[newn..n] + a[n..]
      assert a[newn..] == a[newn..n] + a[n..];
      apply SortedConcat(a[newn..n], a[n..]);
      assert forall i0, j0 :: 0 <= i0 < |a[newn..n]| && 0 <= j0 < |a[n..]| ==> (a[newn..n])[i0] <= (a[n..])[j0] by {
        assume i0, j0 | 0 <= i0 < |a[newn..n]| && 0 <= j0 < |a[n..]|;
        assert newn + i0 < n;
        assert n + j0 < a.Length;
        assert a[newn + i0] <= a[n + j0];
        assert (a[newn..n])[i0] == a[newn + i0];
        assert (a[n..])[j0] == a[n + j0];
      }
    }
    assert forall p, q :: 0 <= p < newn && newn <= q < a.Length ==> a[p] <= a[q] by {
      assume p, q | 0 <= p < newn && newn <= q < a.Length;
      if q < n {
        assert a[p] <= a[q];
      } else {
        assert a[p] <= a[q];
      }
    }

    n := newn;
  }

  if a.Length <= 1 {
    SortedSingleton(a[..]);
  } else {
    // when loop exits with a.Length > 1, we have n <= 1 and invariants give global sortedness
    if n == 0 {
      assert a[0..] == a[n..];
    } else {
      assert n == 1;
      assert Sorted(a[1..]);
      assert forall i, j :: 0 <= i < 1 && 1 <= j < a.Length ==> a[i] <= a[j];
      assert forall j :: 0 <= j < |a[1..]| ==> a[0] <= (a[1..])[j] by {
        assume j | 0 <= j < |a[1..]|;
        assert 1 + j < a.Length;
        assert a[0] <= a[1 + j];
        assert (a[1..])[j] == a[1 + j];
      }
      assert Sorted([a[0]] + a[1..]) by {
        apply SortedConcat([a[0]], a[1..]);
      }
      assert a[..] == [a[0]] + a[1..];
    }
  }
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  assert a[..] == [3, 4, 6, 7];
 }
