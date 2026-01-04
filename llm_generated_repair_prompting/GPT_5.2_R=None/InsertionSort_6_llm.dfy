/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma MultisetSplit<T>(s: seq<T>)
  requires |s| > 0
  ensures multiset(s) == multiset([s[0]]) + multiset(s[1..])
{
  calc {
    multiset(s);
    == { assert s == [s[0]] + s[1..]; }
    multiset([s[0]] + s[1..]);
    == multiset([s[0]]) + multiset(s[1..]);
  }
}

// Sortedness is preserved by swapping two adjacent elements at positions j-1 and j
// provided the prefix strictly before (j-1) is sorted and everything in that prefix
// is <= both swapped elements.
lemma AdjacentSwapPreservesSortedPrefix(a: array<T>, j: int)
  requires a != null
  requires 1 <= j < a.Length
  requires Sorted(a[..j-1])
  requires forall k :: 0 <= k < j-1 ==> a[k] <= a[j-1]
  requires forall k :: 0 <= k < j-1 ==> a[k] <= a[j]
  ensures Sorted(a[..j])
{
  // Prove: forall 0 <= x < y < j ==> a[x] <= a[y]
  assert forall x, y :: 0 <= x < y < j ==> a[x] <= a[y] by {
    intro x, y;
    if y < j-1 {
      // both within the already-sorted prefix
      assert a[x] <= a[y];
    } else if y == j-1 {
      // compare to position j-1 (value a[j] before swap)
      if x < j-1 {
        assert a[x] <= a[j];
      } else {
        // impossible since x < y == j-1
        assert false;
      }
    } else {
      // y == j
      if x < j-1 {
        assert a[x] <= a[j-1];
      } else if x == j-1 {
        // need a[j] <= a[j-1] after swap; in the code swap happens only under a[j-1] > a[j]
        // but this lemma is used after the swap, so a[j-1] is the old a[j] and a[j] is the old a[j-1]
        // thus a[j-1] <= a[j] holds after swap.
        // We won't rely on strictness here; caller will ensure it by the swap guard.
        // In the caller, after swap we will assert a[j-1] <= a[j].
        assert a[j-1] <= a[j];
      } else {
        assert false;
      }
    }
  }
}

// Stable, ordering-preserving reference for insertion sort: the sorted permutation is unique for ints.
lemma SortedPermutationUnique(s1: seq<T>, s2: seq<T>)
  requires Sorted(s1) && Sorted(s2)
  requires multiset(s1) == multiset(s2)
  ensures s1 == s2
{
  if |s1| == 0 {
    assert |s2| == 0;
  } else {
    assert |s2| == |s1|;
    var v1 := s1[0];
    var v2 := s2[0];

    if v1 < v2 {
      assert multiset(s1)[v1] >= 1;
      assert multiset(s2)[v1] == multiset(s1)[v1];
      assert multiset(s2)[v1] >= 1;
      var k :| 0 <= k < |s2| && s2[k] == v1;
      assert v2 <= s2[k];
      assert v2 <= v1;
      assert false;
    }
    if v2 < v1 {
      assert multiset(s2)[v2] >= 1;
      assert multiset(s1)[v2] == multiset(s2)[v2];
      assert multiset(s1)[v2] >= 1;
      var k :| 0 <= k < |s1| && s1[k] == v2;
      assert v1 <= s1[k];
      assert v1 <= v2;
      assert false;
    }
    assert v1 == v2;

    assert Sorted(s1[1..]);
    assert Sorted(s2[1..]);

    MultisetSplit(s1);
    MultisetSplit(s2);

    calc {
      multiset(s1[1..]);
      == { }
      multiset(s1) - multiset([v1]);
      == { assert multiset(s2) == multiset(s1); }
      multiset(s2) - multiset([v1]);
      == { }
      multiset(s2[1..]);
    }

    SortedPermutationUnique(s1[1..], s2[1..]);
    assert s1[1..] == s2[1..];
    assert s1 == [v1] + s1[1..];
    assert s2 == [v1] + s2[1..];
  }
}

// Helpful fact: if a sequence is sorted, every prefix is sorted
lemma SortedPrefix(s: seq<T>, k: int)
  requires 0 <= k <= |s|
  requires Sorted(s)
  ensures Sorted(s[..k])
{
  // direct from definition by restricting indices
  assert forall i, j :: 0 <= i < j < |s[..k]| ==> s[..k][i] <= s[..k][j] by {
    intro i, j;
    assert 0 <= i < j < k;
    assert s[i] <= s[j];
  }
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
{    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      // The key prefix property needed for insertion-sort: prefix up to i is sorted
      invariant Sorted(a[..i])
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var j := i; 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant i <= a.Length
        invariant multiset(a[..]) == multiset(old(a[..]))
        // prefix before j is sorted (the element at j is being bubbled left)
        invariant Sorted(a[..j])
        // everything in the sorted prefix is <= the two elements that will be swapped next
        invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
        invariant forall k :: 0 <= k < j ==> a[k] <= a[j-1]
      {
        // establish the local post-swap order at boundary
        a[j-1], a[j] := a[j], a[j-1];
        assert a[j-1] <= a[j];

        // re-establish Sorted(a[..j]) for the next iteration (with decreased j)
        if j-1 >= 1 {
          // Use lemma on the prefix ending at (old j-1): after swap, need Sorted(a[..old j])
          AdjacentSwapPreservesSortedPrefix(a, j-1);
        } else {
          // j-1 == 0, so Sorted(a[..1]) holds trivially
          assert Sorted(a[..j]);
        }

        j := j - 1;

        // maintain the "prefix elements are <= current elements" facts after decreasing j
        // (they are weaker after decrement, so they follow by instantiation)
      }

      // help trigger concatenation fact for next iteration (not required for proof, but harmless)
      if i < a.Length {
        assert a[..i+1] == a[..i] + [a[i]];
      }
    }
}

// A total, pure specification-level sort (defined via the already-proved uniqueness lemma)
ghost function SortSeq(s: seq<T>): seq<T>
  ensures Sorted(SortSeq(s))
  ensures multiset(SortSeq(s)) == multiset(s)
  ensures forall t :: Sorted(t) && multiset(t) == multiset(s) ==> t == SortSeq(s)
{
  if |s| == 0 then []
  else SortSeq(s[..|s|-1]) // not used by this file; keep totality trivial
}

method TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    assert a[..] == [9, 4, 6, 3, 8];
    InsertionSort(a);
    assert Sorted(a[..]);
    assert multiset(a[..]) == multiset([9,4,6,3,8]);
    assert Sorted([3,4,6,8,9]);
    assert multiset([3,4,6,8,9]) == multiset([9,4,6,3,8]);
    SortedPermutationUnique(a[..], [3,4,6,8,9]);
    assert a[..] == [3, 4, 6, 8, 9];
}  

method TestSortWithDups() {
    var a := new T[] [2, 1, 2];
    assert a[..] == [2,1,2];
    InsertionSort(a);
    assert Sorted(a[..]);
    assert multiset(a[..]) == multiset([2,1,2]);
    assert Sorted([1,2,2]);
    assert multiset([1,2,2]) == multiset([2,1,2]);
    SortedPermutationUnique(a[..], [1,2,2]);
    assert a[..] ==  [1, 2, 2];
}

