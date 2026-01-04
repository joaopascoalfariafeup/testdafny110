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
    // |a[..n]| == n
    assert |a[..n]| == n;
    // a[..n][i] == a[i] for i<n
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

lemma SortedA_SwapStep(a: array<T>, n: int, j: int)
  requires a != null
  requires 0 <= n <= a.Length
  requires 0 < j < n
  requires SortedA(a, n)
  modifies a
  ensures SortedA(a, n)
{
  // Consider the state just after swapping a[j-1] and a[j]
  var oldA := old(a[..]);

  // After the swap, all pairs not involving indices j-1 or j are unchanged and thus remain ordered.
  // We only need to reason about pairs where one index is j-1 or j.
  assert forall p, q :: 0 <= p < q < n && p != j-1 && p != j && q != j-1 && q != j ==> a[p] <= a[q] by {
    assert a[p] == oldA[p] && a[q] == oldA[q];
    // use SortedA(old state) via oldA
    assert forall i, k :: 0 <= i < k < n ==> oldA[i] <= oldA[k] by {
      // from SortedA(a,n) in the pre-state, and oldA captures that pre-state
    }
  }

  // Establish the local ordering facts after the swap:
  // Let x = old a[j-1], y = old a[j], with x > y (since loop guard requires a[j-1] > a[j]).
  // After swap, a[j-1]=y and a[j]=x.
  // For k < j-1: oldA[k] <= oldA[j-1]=x and oldA[k] <= oldA[j]=y because old prefix was sorted.
  // So oldA[k] <= y = a[j-1] and oldA[k] <= x = a[j].
  assert forall k :: 0 <= k < j-1 ==> a[k] <= a[j-1] && a[k] <= a[j] by {
    assert a[k] == oldA[k];
    // From sortedness of oldA:
    assert oldA[k] <= oldA[j-1];
    assert oldA[k] <= oldA[j];
    // After swap:
    assert a[j-1] == oldA[j];
    assert a[j] == oldA[j-1];
  }

  // For k > j: oldA[j-1] <= oldA[k] and oldA[j] <= oldA[k].
  // After swap, a[j]=oldA[j-1] and a[j-1]=oldA[j], so both <= a[k].
  assert forall k :: j+1 <= k < n ==> a[j-1] <= a[k] && a[j] <= a[k] by {
    assert a[k] == oldA[k];
    assert oldA[j-1] <= oldA[k];
    assert oldA[j] <= oldA[k];
    assert a[j-1] == oldA[j];
    assert a[j] == oldA[j-1];
  }

  // Also ensure the pair (j-1, j) itself is ordered after swap:
  assert a[j-1] <= a[j] by {
    assert a[j-1] == oldA[j];
    assert a[j] == oldA[j-1];
    // old prefix sorted implies oldA[j-1] <= oldA[j]
    assert oldA[j-1] <= oldA[j];
  }

  // Now conclude full SortedA(a,n)
  assert 0 <= n <= a.Length;
  assert forall p, q :: 0 <= p < q < n ==> a[p] <= a[q] by {
    if p == j-1 && q == j {
      assert a[p] <= a[q];
    } else if p == j-1 && q > j {
      assert a[p] <= a[q] by { assert a[j-1] <= a[q]; }
    } else if p == j && q > j {
      assert a[p] <= a[q] by { assert a[j] <= a[q]; }
    } else if q == j-1 {
      // then p < j-1
      assert a[p] <= a[q] by { assert a[p] <= a[j-1]; }
    } else if q == j {
      if p == j-1 {
        assert a[p] <= a[q];
      } else {
        // p < j-1
        assert a[p] <= a[q] by { assert a[p] <= a[j]; }
      }
    } else {
      // neither p nor q is j-1 or j
      assert a[p] <= a[q] by {
        assert a[p] == oldA[p] && a[q] == oldA[q];
        // old state sorted:
        assert oldA[p] <= oldA[q];
      }
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
        // At inner-loop exit, either j==0 or a[j-1] <= a[j]; combined with SortedA(a,i),
        // we get that all elements in 0..i-1 are <= a[i].
        assert forall k :: 0 <= k < i ==> a[k] <= a[i] by {
          if i == 0 {
          } else if j == 0 {
            // From SortedA(a,i): a[k] <= a[i-1] for k<i-1.
            if k < i-1 {
              assert a[k] <= a[i-1];
            }
            // Also need a[i-1] <= a[i]. The inner loop starting at j=i would still be running if a[i-1] > a[i].
            if a[i-1] > a[i] {
              // then guard would hold at j=i, contradicting termination
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
            // j > 0 and the guard is false, so a[j-1] <= a[j]
            assert a[j-1] <= a[j];
            // Since SortedA(a,i), a[j-1] is >= every element before it, and a[j] (which is a[i]) is >= a[j-1].
            if k < j {
              assert a[k] <= a[j-1];
              assert a[j-1] <= a[j];
              assert a[k] <= a[j];
            } else if k == j {
              // when j<i, a[j] is within sorted prefix; still <= a[i] (which equals a[i])
              if j == i {
                assert a[k] <= a[i];
              } else {
                assert a[k] <= a[i-1];
                // and as above a[i-1] <= a[i] follows because otherwise guard would be true at j=i initially,
                // but in this branch we only need a[k] <= a[i], which holds since a[i] is a[j] when j==i;
                // if j<i, then k==j implies a[k]==a[j] and we already established a[j-1] <= a[j].
                assert a[k] <= a[i];
              }
            } else {
              // j < k < i
              assert a[k] <= a[i-1];
              // show a[i-1] <= a[i] similarly (otherwise loop would have continued from j=i)
              if i > 0 && a[i-1] > a[i] {
                assert j > 0 && a[j-1] > a[j];
              }
              if i > 0 { assert a[i-1] <= a[i]; }
              assert a[k] <= a[i];
            }
          }
        }

        SortedA_ExtendByOne(a, i);

        // help the verifier connect prefix-extension to sequences (optional)
        assert a[..i+1] == a[..i] + [a[i]];
      }
    }

    // discharge postcondition Sorted(a[..]) from SortedA(a,a.Length)
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
