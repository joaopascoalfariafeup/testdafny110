/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// ---------- Proof-oriented ghost utilities for tests ----------

ghost function {:fuel 20} Min(s: seq<int>): int
  requires |s| > 0
  ensures Min(s) in s
  ensures forall k :: 0 <= k < |s| ==> Min(s) <= s[k]
{
  if |s| == 1 then s[0]
  else
    var m := Min(s[..|s|-1]);
    if s[|s|-1] < m then s[|s|-1] else m
}

ghost function RemoveOne(s: seq<int>, x: int): seq<int>
  ensures |RemoveOne(s, x)| <= |s|
{
  if |s| == 0 then []
  else if s[0] == x then s[1..]
  else [s[0]] + RemoveOne(s[1..], x)
}

lemma RemoveOneRemovesExactlyOne(s: seq<int>, x: int)
  requires x in s
  ensures multiset(RemoveOne(s, x)) == multiset(s) - multiset([x])
{
  if |s| == 0 {
  } else if s[0] == x {
    // RemoveOne(s,x) == s[1..]
    assert s == [s[0]] + s[1..];
    assert multiset(s) == multiset([x]) + multiset(s[1..]);
  } else {
    assert x in s[1..];
    RemoveOneRemovesExactlyOne(s[1..], x);
    assert RemoveOne(s, x) == [s[0]] + RemoveOne(s[1..], x);
    assert s == [s[0]] + s[1..];
    calc {
      multiset(RemoveOne(s, x));
      == multiset([s[0]] + RemoveOne(s[1..], x));
      == multiset([s[0]]) + multiset(RemoveOne(s[1..], x));
      == multiset([s[0]]) + (multiset(s[1..]) - multiset([x]));
      == (multiset([s[0]]) + multiset(s[1..])) - multiset([x]);
      == multiset(s) - multiset([x]);
    }
  }
}

ghost function {:fuel 20} SortSeq(s: seq<int>): seq<int>
  ensures Sorted(SortSeq(s))
  ensures multiset(SortSeq(s)) == multiset(s)
{
  if |s| == 0 then []
  else
    var m := Min(s);
    [m] + SortSeq(RemoveOne(s, m))
}

lemma SortedTailIsSorted(s: seq<int>)
  requires Sorted(s)
  ensures Sorted(s[1..])
{
}

lemma SortedFirstLeAll(s: seq<int>, k: int)
  requires Sorted(s)
  requires 0 <= k < |s|
  ensures s[0] <= s[k]
{
  if k == 0 {
  } else {
    assert 0 <= 0 < k < |s|;
  }
}

lemma SortedMultisetImpliesEqualsSort(t: seq<int>, s: seq<int>)
  requires Sorted(t)
  requires multiset(t) == multiset(s)
  ensures t == SortSeq(s)
{
  if |s| == 0 {
    assert multiset(t) == multiset([]);
    assert |t| == 0;
  } else {
    assert |t| == |s|;
    var m := Min(s);
    assert m in s;
    assert multiset([m]) <= multiset(s);
    assert multiset([m]) <= multiset(t);
    assert m in t;

    // Show t[0] == m
    SortedFirstLeAll(t, 0);
    // t[0] <= every element of t, in particular <= m
    assert t[0] <= m by {
      // since m in t, pick an index where it occurs
      var idx :| 0 <= idx < |t| && t[idx] == m;
      SortedFirstLeAll(t, idx);
    }

    // m <= every element of s, hence (via equal multiset) every element of t
    assert m <= t[0] by {
      // t[0] is an element of t, hence appears in s
      assert multiset([t[0]]) <= multiset(t);
      assert multiset([t[0]]) <= multiset(s);
      assert t[0] in s;
      var idx :| 0 <= idx < |s| && s[idx] == t[0];
      assert m <= s[idx];
      assert s[idx] == t[0];
    }

    assert t[0] == m;

    // Induction on the tail
    assert Sorted(t[1..]) by { SortedTailIsSorted(t); }
    RemoveOneRemovesExactlyOne(s, m);
    assert multiset(t[1..]) == multiset(t) - multiset([t[0]]);
    assert multiset(t[1..]) == multiset(s) - multiset([m]);
    assert multiset(t[1..]) == multiset(RemoveOne(s, m));

    SortedMultisetImpliesEqualsSort(t[1..], RemoveOne(s, m));

    // Conclude whole sequence equality
    assert t == [t[0]] + t[1..];
    assert SortSeq(s) == [m] + SortSeq(RemoveOne(s, m));
    calc {
      t;
      == [t[0]] + t[1..];
      == [m] + SortSeq(RemoveOne(s, m));
      == SortSeq(s);
    }
  }
}

// ---------- SwapSeq used inside the algorithm proof ----------

function SwapSeq(s: seq<T>, i: int, j: int): seq<T>
  requires 0 <= i < |s|
  requires 0 <= j < |s|
{
  if i == j then s
  else if i < j then
    s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]
  else
    s[..j] + [s[i]] + s[j+1..i] + [s[j]] + s[i+1..]
}

lemma SwapSeqMultiset(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(SwapSeq(s, i, j)) == multiset(s)
{
  if i == j {
  } else if i < j {
    assert s == s[..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..];
    calc {
      multiset(SwapSeq(s, i, j));
      == multiset(s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]);
      == multiset(s[..i]) + multiset([s[j]]) + multiset(s[i+1..j]) + multiset([s[i]]) + multiset(s[j+1..]);
      == multiset(s[..i]) + multiset([s[i]]) + multiset(s[i+1..j]) + multiset([s[j]]) + multiset(s[j+1..]);
      == multiset(s[..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..]);
      == multiset(s);
    }
  } else {
    // j < i
    assert s == s[..j] + [s[j]] + s[j+1..i] + [s[i]] + s[i+1..];
    calc {
      multiset(SwapSeq(s, i, j));
      == multiset(s[..j] + [s[i]] + s[j+1..i] + [s[j]] + s[i+1..]);
      == multiset(s[..j]) + multiset([s[i]]) + multiset(s[j+1..i]) + multiset([s[j]]) + multiset(s[i+1..]);
      == multiset(s[..j]) + multiset([s[j]]) + multiset(s[j+1..i]) + multiset([s[i]]) + multiset(s[i+1..]);
      == multiset(s[..j] + [s[j]] + s[j+1..i] + [s[i]] + s[i+1..]);
      == multiset(s);
    }
  }
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
{    
    ghost var ms0 := multiset(a[..]);

    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant multiset(a[..]) == ms0
    {
      var j := i; 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant 0 <= i < a.Length ==> i + 1 <= a.Length
        invariant multiset(a[..]) == ms0
        invariant forall p, q :: 0 <= p < q < i + 1 ==> q == j || a[p] <= a[q]
      {
        ghost var before := a[..];
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        assert a[..] == SwapSeq(before, j-1, j);
        SwapSeqMultiset(before, j-1, j);
        assert multiset(a[..]) == multiset(before);
        j := j - 1;
      }

      // At loop exit: j == 0 || a[j-1] <= a[j]
      if j > 0 {
        assert a[j-1] <= a[j];
      }

      assert Sorted(a[..i+1]) by {
        forall p, q | 0 <= p < q < i + 1
          ensures a[p] <= a[q]
        {
          if q == j {
            // Here q==j implies j>0 (since p<q), so a[j-1] <= a[j] is available
            if p == q - 1 {
              assert a[p] <= a[q];
            } else {
              assert p < q - 1;
              // use the while-loop invariant for (p, q-1), since q-1 != j
              assert a[p] <= a[q-1];
              assert a[q-1] <= a[q];
              assert a[p] <= a[q];
            }
          } else {
            // direct from the while-loop invariant
            assert a[p] <= a[q];
          }
        }
      }
      assert Sorted(a[..i+1]);
    }
}


method TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    InsertionSort(a);

    // Help Dafny connect the postconditions to the concrete expected result
    SortedMultisetImpliesEqualsSort(a[..], [9, 4, 6, 3, 8]);
    assert SortSeq([9, 4, 6, 3, 8]) == [3, 4, 6, 8, 9];

    assert a[..] == [3, 4, 6, 8, 9];
}  

method TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    InsertionSort(a);

    SortedMultisetImpliesEqualsSort(a[..], [2, 1, 2]);
    assert SortSeq([2, 1, 2]) == [1, 2, 2];

    assert a[..] ==  [1, 2, 2];
}

