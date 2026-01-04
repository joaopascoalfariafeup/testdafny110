/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures perm(a[..], old(a[..]))
  ensures sorted(a[..])
{
    // In each iteration, find the minimum value in the unsorted part of the array
    // (on the right) and append it (by swapping) to the sorted part (on the left).
    for i := 0 to a.Length 
      invariant 0 <= i <= a.Length
      invariant perm(a[..], old(a[..]))
      invariant sorted(a[..i])
      invariant forall k, l :: 0 <= k < i && i <= l < a.Length ==> a[k] <= a[l]
    {
        // Find the minimum value in the unsorted part of the array
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i + 1 <= j <= a.Length + 1
          invariant i <= jMin < a.Length
          invariant forall k :: i <= k < j ==> a[jMin] <= a[k]
          invariant forall k :: i <= k < jMin ==> a[k] == old(a[k])
          invariant forall k :: jMin < k < j ==> a[k] == old(a[k])
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

predicate sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate perm(a: seq<int>, b: seq<int>) {
  multiset(a) == multiset(b)
}

// Helper lemma to prove the test assertion
lemma TestHelper(a: array<int>, expected: seq<int>)
  requires a.Length == |expected|
  requires perm(a[..], expected)
  requires sorted(a[..])
  requires sorted(expected)
  ensures a[..] == expected
{
  // If two sequences have the same multiset and are both sorted,
  // they must be equal
  if a[..] != expected {
    var i := 0;
    while i < a.Length && a[i] == expected[i]
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> a[j] == expected[j]
    {
      i := i + 1;
    }
    if i < a.Length {
      if a[i] < expected[i] {
        // a[i] appears in expected since multisets are equal
        // but expected is sorted, so all elements after i are >= expected[i] > a[i]
        // so a[i] must appear before position i in expected
        // but that contradicts that a[0..i] == expected[0..i]
        // Show contradiction using multiset properties
        assert a[i] in multiset(expected);
        assert forall j :: 0 <= j < i ==> expected[j] == a[j];
        assert forall j :: i <= j < a.Length ==> expected[j] >= expected[i];
        // Since a[i] < expected[i], a[i] must be in expected[0..i-1]
        // But expected[0..i-1] == a[0..i-1], and a[i] is not in a[0..i-1] because a is sorted
        // and a[i] >= all elements in a[0..i-1]
        assert forall j :: 0 <= j < i ==> a[j] <= a[i];
        // Contradiction: a[i] cannot be in expected[0..i-1] because those values are <= a[i]
        // but a[i] < expected[i] and expected[i] is the smallest among expected[i..]
        assert false;
      } else {
        // symmetric case: expected[i] < a[i]
        assert expected[i] in multiset(a[..]);
        assert forall j :: 0 <= j < i ==> a[j] == expected[j];
        assert forall j :: i <= j < a.Length ==> a[j] >= a[i];
        // Since expected[i] < a[i], expected[i] must be in a[0..i-1]
        // But a[0..i-1] == expected[0..i-1], and expected[i] is not in expected[0..i-1] because expected is sorted
        // and expected[i] >= all elements in expected[0..i-1]
        assert forall j :: 0 <= j < i ==> expected[j] <= expected[i];
        // Contradiction
        assert false;
      }
    }
  }
}

// Test case checked statically.
method testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  SelectionSort(a);
  // Use the helper lemma to prove the final assertion
  var expected := [1, 4, 6, 8, 9];
  // Prove preconditions for TestHelper
  assert a.Length == 5;
  assert |expected| == 5;
  assert sorted(a[..]);
  assert sorted(expected);
  // Prove perm(a[..], expected) by showing multiset equality
  // Since SelectionSort ensures perm(a[..], old(a[..])), and old(a[..]) = [9,4,6,1,8]
  // and expected = [1,4,6,8,9] has the same multiset
  assert multiset([9,4,6,1,8]) == multiset([1,4,6,8,9]);
  TestHelper(a, expected);
  assert a[..] == [1, 4, 6, 8, 9];
}

