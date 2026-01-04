/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma MultisetMemberImpliesSeqMember(x: int, s: seq<int>)
  requires x in multiset(s)
  ensures x in s
  decreases |s|
{
  if |s| == 0 {
  } else {
    if s[0] == x {
    } else {
      assert x in multiset(s[1..]);
      MultisetMemberImpliesSeqMember(x, s[1..]);
    }
  }
}

lemma SortedByMultisetUnique(s: seq<int>, t: seq<int>)
  requires |s| == |t|
  requires Sorted(s)
  requires Sorted(t)
  requires multiset(s) == multiset(t)
  ensures s == t
  decreases |s|
{
  if |s| == 0 {
  } else {
    var s0 := s[0];
    var t0 := t[0];

    assert s0 in multiset(t);
    MultisetMemberImpliesSeqMember(s0, t);
    assert s0 in t;
    assert exists k :: 0 <= k < |t| && t[k] == s0;
    var k :| 0 <= k < |t| && t[k] == s0;
    assert t0 <= t[k];
    assert t0 <= s0;

    assert t0 in multiset(s);
    MultisetMemberImpliesSeqMember(t0, s);
    assert t0 in s;
    assert exists m :: 0 <= m < |s| && s[m] == t0;
    var m :| 0 <= m < |s| && s[m] == t0;
    assert s0 <= s[m];
    assert s0 <= t0;

    assert s0 == t0;

    assert multiset(s[1..]) == multiset(t[1..]);
    SortedByMultisetUnique(s[1..], t[1..]);
  }
}

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
    // In each iteration, find the minimum value in the unsorted part of the array
    // (on the right) and append it (by swapping) to the sorted part (on the left).
    for i := 0 to a.Length 
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant forall k, l :: 0 <= k < i && i <= l < a.Length ==> a[k] <= a[l]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i + 1 <= j <= a.Length
          invariant i <= jMin < j
          invariant forall k :: i <= k < j ==> a[jMin] <= a[k]
          invariant multiset(a[..]) == old(multiset(a[..]))
        {
            if a[j] < a[jMin] {
                jMin := j;
            }
        } 
        // Swap it with the first unsorted element
        if jMin != i {
          a[i], a[jMin] := a[jMin], a[i]; 
        }
    }
}


// Test case checked statically.
method testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  SelectionSort(a);
  assert Sorted(a[..]);
  assert multiset(a[..]) == multiset([9, 4, 6, 1, 8]);
  assert Sorted([1, 4, 6, 8, 9]);
  assert multiset([1, 4, 6, 8, 9]) == multiset([9, 4, 6, 1, 8]);
  SortedByMultisetUnique(a[..], [1, 4, 6, 8, 9]);
  assert a[..] == [1, 4, 6, 8, 9];
}
