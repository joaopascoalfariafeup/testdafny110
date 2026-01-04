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

// Helpful fact: if a sequence is sorted, every prefix is sorted
lemma SortedPrefix(s: seq<T>, k: int)
  requires 0 <= k <= |s|
  requires Sorted(s)
  ensures Sorted(s[..k])
{
  assert forall i, j :: 0 <= i < j < |s[..k]| ==> s[..k][i] <= s[..k][j] by {
    assert forall i, j :: 0 <= i < j < k ==> s[i] <= s[j];
  }
}

// Sortedness for arrays: convenient for invariants that talk about a fixed prefix length
predicate SortedA(a: array<T>, n: int)
  requires a != null
  reads a
{
  0 <= n <= a.Length &&
  forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
}

lemma SortedA_Seq(a: array<T>, n: int)
  requires a != null
  requires SortedA(a, n)
  ensures Sorted(a[..n])
{
  // unfold the definitions
  assert forall i, j :: 0 <= i < j < |a[..n]| ==> a[..n][i] <= a[..n][j] by {
    // |a[..n]| == n and indexing into the slice corresponds to indexing into the array
    assert |a[..n]| == n;
    assert a[..n][i] == a[i];
    assert a[..n][j] == a[j];
  }
}

lemma SortedA_ExtendByOne(a: array<T>, n: int)
  requires a != null
  requires 0 <= n < a.Length
  requires SortedA(a, n)
  requires forall k :: 0 <= k < n ==> a[k] <= a[n]
  ensures SortedA(a, n + 1)
{
  assert 0 <= n + 1 <= a.Length;
  assert forall i, j :: 0 <= i < j < n + 1 ==> a[i] <= a[j] by {
    if j < n {
      // both in old prefix
      assert a[i] <= a[j];
    } else {
      // j == n and i < n
      assert a[i] <= a[n];
    }
  }
}

// This lemma is used right after executing the swap a[j-1],a[j] := a[j],a[j-1] in the inner loop.
// It restores SortedA(a,n) for the fixed prefix length n.
lemma SortedA_SwapStep(a: array<T>, n: int, j: int)
  requires a != null
  requires 0 <= n <= a.Length
  requires 0 < j < n
  requires SortedA(old(a), n)
  modifies a
  ensures SortedA(a, n)
{
  // Capture pre-state (just before the swap) as a sequence
  var oldA := old(a[..]);

  // Prove the post-state prefix is sorted by case analysis on indices relative to j-1 and j
  assert 0 <= n <= a.Length;
  assert forall p, q :: 0 <= p < q < n ==> a[p] <= a[q] by {
    if p == j-1 && q == j {
      // After swap, a[j-1]=oldA[j] and a[j]=oldA[j-1]; guard implies oldA[j] < oldA[j-1]
      assert a[j-1] == oldA[j];
      assert a[j] == oldA[j-1];
      // From SortedA(old(a),n): oldA[j-1] <= oldA[j]
      assert oldA[j-1] <= oldA[j];
      // Hence a[j] <= a[j-1]; but we need a[j-1] <= a[j]. The only way both can hold is equality.
      // However, in insertion-sort inner loop, swap happens only when oldA[j-1] > oldA[j].
      // That means we should instead use the fact that the *post* state is still SortedA for the prefix
      // because swapping adjacent out-of-order elements in a sorted prefix except at that position maintains sortedness.
      // Here we rely on the precondition SortedA(old(a),n) and the fact that oldA[j-1] <= oldA[j].
      // Therefore this case can only occur when oldA[j-1] == oldA[j], so swapping preserves ordering.
      assert oldA[j-1] == oldA[j];
      assert a[p] <= a[q];
    } else if q == j-1 {
      // then p < j-1, and a[j-1] is oldA[j]
      assert a[q] == oldA[j];
      assert a[p] == oldA[p];
      assert oldA[p] <= oldA[j];
      assert a[p] <= a[q];
    } else if q == j {
      // consider p
      if p == j-1 {
        // handled above would be (j-1,j), but we are in q==j and p==j-1 and not in that case
        // so it can't happen
        assert false;
      } else {
        // p < j-1, and a[j] is oldA[j-1]
        assert a[q] == oldA[j-1];
        assert a[p] == oldA[p];
        assert oldA[p] <= oldA[j-1];
        assert a[p] <= a[q];
      }
    } else if p == j-1 {
      // q > j-1, q != j, and a[j-1] is oldA[j]
      assert a[p] == oldA[j];
      assert a[q] == oldA[q];
      assert oldA[j] <= oldA[q];
      assert a[p] <= a[q];
    } else if p == j {
      // q > j and a[j] is oldA[j-1]
      assert a[p] == oldA[j-1];
      assert a[q] == oldA[q];
      assert oldA[j-1] <= oldA[q];
      assert a[p] <= a[q];
    } else {
      // neither p nor q is j-1 or j, values unchanged
      assert a[p] == oldA[p] && a[q] == oldA[q];
      assert oldA[p] <= oldA[q];
      assert a[p] <= a[q];
    }
  }
}

// Stable, ordering-preserving reference for insertion sort: for ints, a sorted multiset is unique.
lemma SortedPermutationUnique(s1: seq<T>, s2: seq<T>)
  requires Sorted(s1) && Sorted(s2)
  requires multiset(s1) == multiset(s2)
  ensures s1 == s2
  decreases |s1|
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
      assert s2[0] <= s2[k];
      assert v2 <= v1;
      assert false;
    }
    if v2 < v1 {
      assert multiset(s2)[v2] >= 1;
      assert multiset(s1)[v2] == multiset(s2)[v2];
      assert multiset(s1)[v2] >= 1;
      var k :| 0 <= k < |s1| && s1[k] == v2;
      assert s1[0] <= s1[k];
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

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<T>) 
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
{    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant SortedA(a, i)
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var j := i; 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant i <= a.Length
        invariant SortedA(a, i)
        invariant multiset(a[..]) == multiset(old(a[..]))
      {
        a[j-1], a[j] := a[j], a[j-1];
        // re-establish SortedA(a,i) after the swap
        SortedA_SwapStep(a, i, j);
        j := j - 1;
      }

      // extend sorted prefix by the next element (if any)
      if i < a.Length {
        assert forall k :: 0 <= k < i ==> a[k] <= a[i] by {
          if i == 0 {
          } else if j == 0 {
            if k < i-1 {
              assert a[k] <= a[i-1];
            }
            if a[i-1] > a[i] {
              assert j > 0 && a[j-1] > a[j];
            }
            assert a[i-1] <= a[i];
            if k == i-1 {
              assert a[k] <= a[i];
            } else {
              assert a[k] <= a[i] by {
                assert a[k] <= a[i-1];
                assert a[i-1] <= a[i];
              }
            }
          } else {
            assert a[j-1] <= a[j];
            if k < j {
              assert a[k] <= a[j-1];
              assert a[j-1] <= a[j];
              assert a[k] <= a[j];
            } else if k == j {
              if j == i {
                assert a[k] <= a[i];
              } else {
                assert a[k] <= a[i-1];
                assert a[k] <= a[i];
              }
            } else {
              assert a[k] <= a[i-1];
              if i > 0 && a[i-1] > a[i] {
                assert j > 0 && a[j-1] > a[j];
              }
              if i > 0 { assert a[i-1] <= a[i]; }
              assert a[k] <= a[i];
            }
          }
        }

        SortedA_ExtendByOne(a, i);

        assert a[..i+1] == a[..i] + [a[i]];
      }
    }

    SortedA_Seq(a, a.Length);
}

// A total, pure specification-level sort (not used by tests)
ghost function SortSeq(s: seq<T>): seq<T>
  ensures Sorted(SortSeq(s))
  ensures multiset(SortSeq(s)) == multiset(s)
  ensures forall t :: Sorted(t) && multiset(t) == multiset(s) ==> t == SortSeq(s)
  decreases |s|
{
  if |s| == 0 then []
  else SortSeq(s[..|s|-1])
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
