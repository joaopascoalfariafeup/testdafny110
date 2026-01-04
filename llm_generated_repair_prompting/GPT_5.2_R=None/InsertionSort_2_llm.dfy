/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another comparable type

predicate Sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Stable, ordering-preserving reference for insertion sort: the sorted permutation is unique for ints.
lemma SortedPermutationUnique(s1: seq<T>, s2: seq<T>)
  requires Sorted(s1) && Sorted(s2)
  requires multiset(s1) == multiset(s2)
  ensures s1 == s2
{
  if |s1| == 0 {
  } else {
    // show first elements equal by contradiction on counts of <= v
    var v1 := s1[0];
    var v2 := s2[0];

    // helper: in a sorted sequence, v is the first element iff count(x <= v) >= 1 and count(x < v) == 0
    // We'll use multiset equality directly via contradiction:
    // Suppose v1 < v2. Then s1 has an element v1 that is < v2, hence s2 must also,
    // but Sorted(s2) and v2 = s2[0] forbids any element < v2.
    if v1 < v2 {
      // In s1, element v1 exists and is < v2
      assert multiset(s1)[v1] >= 1;
      // multiset equal => s2 also contains v1
      assert multiset(s2)[v1] == multiset(s1)[v1];
      assert multiset(s2)[v1] >= 1;
      // Hence some index in s2 has value v1
      var k :| 0 <= k < |s2| && s2[k] == v1;
      // But then s2[0] <= s2[k] (sorted) so v2 <= v1, contradiction to v1 < v2
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

    // Remove one occurrence of v1 from both and apply IH to tails
    // Since sorted and first elements equal, tails are sorted.
    assert Sorted(s1[1..]);
    assert Sorted(s2[1..]);

    // multiset(s[1..]) == multiset(s) - {s[0]}
    assert multiset(s1) == multiset([s1[0]]) + multiset(s1[1..]);
    assert multiset(s2) == multiset([s2[0]]) + multiset(s2[1..]);
    calc {
      multiset(s1[1..]);
      == { assert multiset(s1) == multiset([v1]) + multiset(s1[1..]); }
      multiset(s1) - multiset([v1]);
      == { assert multiset(s2) == multiset(s1); }
      multiset(s2) - multiset([v1]);
      == { assert multiset(s2) == multiset([v1]) + multiset(s2[1..]); }
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
    // In each iteration, it picks the next element from the unsorted part of the array (on the right)
    // and inserts it into the correct position in the sorted part of the array (on the left).  
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var j := i; 
      // Move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant i <= a.Length
        // keep the already-sorted prefix before j
        invariant Sorted(a[..j])
        // avoid ill-formed slice when j == i
        invariant j < i ==> Sorted(a[j+1..i])
        invariant j < i ==> (forall k :: j < k < i ==> a[j] <= a[k])
        // only mention a[j] when j < i (otherwise a[j] is outside a[..i])
        invariant j < i ==> (forall k :: 0 <= k < j ==> a[k] <= a[j])
        // permutation maintained for full array (suffices)
        invariant multiset(a[..]) == multiset(old(a[..]))
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
      // Help Dafny re-establish Sorted(a[..i+1]) at next loop head
      if i < a.Length {
        assert a[..i+1] == a[..i] + [a[i]];
      }
    }
}

// A small ghost sorting spec used only by tests to pin down the exact expected sequence
ghost function {:termination false} SortSeq(s: seq<T>): seq<T>
  ensures Sorted(SortSeq(s))
  ensures multiset(SortSeq(s)) == multiset(s)
{
  if |s| <= 1 then s
  else
    // definition via abstract existence; uniqueness lemma lets tests conclude equality
    (var t :| Sorted(t) && multiset(t) == multiset(s); t)
}

method TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    assert a[..] == [9, 4, 6, 3, 8];
    InsertionSort(a);
    // use uniqueness of sorted permutation to conclude exact order
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
