/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/



predicate Sorted(s: seq<int>)
{
  forall k :: 0 < k < |s| ==> s[k-1] <= s[k]
}

lemma SortedMonotone(s: seq<int>, i: int, j: int)
  requires Sorted(s)
  requires 0 <= i <= j < |s|
  ensures s[i] <= s[j]
  decreases j - i
{
  if i == j {
  } else {
    SortedMonotone(s, i, j - 1);
    assert s[j - 1] <= s[j];
  }
}

lemma SortedMultiset_7346_Unique(s: seq<int>)
  requires |s| == 4
  requires Sorted(s)
  requires multiset(s) == multiset([7, 3, 4, 6])
  ensures s == [3, 4, 6, 7]
{
  assert multiset(s)[3] == 1;
  assert multiset(s)[4] == 1;
  assert multiset(s)[6] == 1;
  assert multiset(s)[7] == 1;

  assert s[0] == 3
  by {
    if s[0] != 3 {
      assert multiset(s)[s[0]] >= 1;
      assert s[0] != 4 && s[0] != 6 && s[0] != 7 by {
        if s[0] == 4 {
          SortedMonotone(s, 0, 3);
          assert s[0] <= s[3];
          assert multiset(s)[3] == 0;
          assert false;
        } else if s[0] == 6 {
          SortedMonotone(s, 0, 3);
          assert s[0] <= s[3];
          assert multiset(s)[3] == 0;
          assert false;
        } else if s[0] == 7 {
          SortedMonotone(s, 0, 3);
          assert s[0] <= s[3];
          assert multiset(s)[3] == 0;
          assert false;
        }
      }
      assert false;
    }
  }

  assert s[3] == 7
  by {
    if s[3] != 7 {
      assert s[3] == 3 || s[3] == 4 || s[3] == 6 by {
        if s[3] == 3 {
          SortedMonotone(s, 0, 3);
          assert s[0] <= s[3];
          assert s[0] == 3;
          assert multiset(s)[7] == 0;
          assert false;
        } else if s[3] == 4 {
          SortedMonotone(s, 0, 3);
          assert s[0] <= s[3];
          assert s[0] == 3;
          assert multiset(s)[7] == 0;
          assert false;
        } else if s[3] == 6 {
          SortedMonotone(s, 0, 3);
          assert s[0] <= s[3];
          assert s[0] == 3;
          assert multiset(s)[7] == 0;
          assert false;
        }
      }
      assert false;
    }
  }

  assert s[1] == 4
  by {
    if s[1] != 4 {
      assert s[1] == 6 by {
        if s[1] == 3 {
          SortedMonotone(s, 0, 1);
          assert s[0] <= s[1];
          assert s[0] == 3;
          assert multiset(s)[4] == 0;
          assert false;
        } else if s[1] == 7 {
          SortedMonotone(s, 1, 3);
          assert s[1] <= s[3];
          assert s[3] == 7;
          assert multiset(s)[4] == 0;
          assert false;
        } else if s[1] == 6 {
        } else if s[1] == 4 {
        }
      }
      if s[1] == 6 {
        SortedMonotone(s, 1, 2);
        assert s[1] <= s[2];
        assert s[2] == 7 || s[2] == 6 || s[2] == 4 || s[2] == 3;
        assert s[2] != 4 by {
          if s[2] == 4 {
            assert multiset(s)[6] == 0;
            assert false;
          }
        }
        assert s[2] == 4;
        assert false;
      }
    }
  }

  assert s[2] == 6
  by {
    if s[2] != 6 {
      assert s[2] == 4 by {
        if s[2] == 3 {
          SortedMonotone(s, 0, 2);
          assert s[0] <= s[2];
          assert s[0] == 3;
          assert multiset(s)[6] == 0;
          assert false;
        } else if s[2] == 4 {
        } else if s[2] == 7 {
          SortedMonotone(s, 2, 3);
          assert s[2] <= s[3];
          assert s[3] == 7;
          assert multiset(s)[6] == 0;
          assert false;
        }
      }
      assert s[1] == 4;
      SortedMonotone(s, 1, 2);
      assert s[1] <= s[2];
      assert s[2] != 4;
      assert false;
    }
  }
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  ghost var ms0 := multiset(a[..]);

  var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

  // Does multiple passes over the array, each time bubbling the largest element to the right-hand side.
  while n  > 1
    invariant 0 <= n <= a.Length
    invariant multiset(a[..]) == ms0
    invariant Sorted(a[n..])
  {
    // Scans the array a[..n] from left to right, swapping adjacent elements if they
    // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
    var newn : nat := 0;
    for i := 1 to n
      invariant 1 <= i <= n
      invariant 0 <= newn < n
      invariant multiset(a[..]) == ms0
      invariant Sorted(a[n..])
      invariant forall k :: 0 <= k < i ==> a[k] <= a[i-1]
    {
      if (a[i-1] > a[i]) { 
        a[i-1], a[i] := a[i], a[i-1]; 
        newn := i;
      }
      assert a[i-1] <= a[i] || i == n; // harmless strengthening for the max invariant step
    }
    n := newn;
  }
  assert multiset(a[..]) == ms0;
}

// A simple test case checked statically.
method TestBubbleSort() {
  var a := new int[] [7, 3, 4, 6];
  BubbleSort(a);
  ghost var s := a[..];
  assert Sorted(s);
  assert multiset(s) == multiset([7, 3, 4, 6]);
  SortedMultiset_7346_Unique(s);
  assert a[..] == [3, 4, 6, 7];
 }
