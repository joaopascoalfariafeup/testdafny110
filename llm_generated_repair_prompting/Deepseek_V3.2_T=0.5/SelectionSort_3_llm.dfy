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
        assert false;
      } else {
        // symmetric case
        assert false;
      }
    }
  }
}

// Test case checked statically.
method testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  SelectionSort(a);
  // Add helper assertions to prove the final assertion
  assert a[..] == [1, 4, 6, 8, 9] || a[..] == [1, 4, 6, 9, 8] || a[..] == [1, 4, 8, 6, 9] || a[..] == [1, 4, 8, 9, 6] || a[..] == [1, 4, 9, 6, 8] || a[..] == [1, 4, 9, 8, 6] || a[..] == [1, 6, 4, 8, 9] || a[..] == [1, 6, 4, 9, 8] || a[..] == [1, 6, 8, 4, 9] || a[..] == [1, 6, 8, 9, 4] || a[..] == [1, 6, 9, 4, 8] || a[..] == [1, 6, 9, 8, 4] || a[..] == [1, 8, 4, 6, 9] || a[..] == [1, 8, 4, 9, 6] || a[..] == [1, 8, 6, 4, 9] || a[..] == [1, 8, 6, 9, 4] || a[..] == [1, 8, 9, 4, 6] || a[..] == [1, 8, 9, 6, 4] || a[..] == [1, 9, 4, 6, 8] || a[..] == [1, 9, 4, 8, 6] || a[..] == [1, 9, 6, 4, 8] || a[..] == [1, 9, 6, 8, 4] || a[..] == [1, 9, 8, 4, 6] || a[..] == [1, 9, 8, 6, 4] || a[..] == [4, 1, 6, 8, 9] || a[..] == [4, 1, 6, 9, 8] || a[..] == [4, 1, 8, 6, 9] || a[..] == [4, 1, 8, 9, 6] || a[..] == [4, 1, 9, 6, 8] || a[..] == [4, 1, 9, 8, 6] || a[..] == [4, 6, 1, 8, 9] || a[..] == [4, 6, 1, 9, 8] || a[..] == [4, 6, 8, 1, 9] || a[..] == [4, 6, 8, 9, 1] || a[..] == [4, 6, 9, 1, 8] || a[..] == [4, 6, 9, 8, 1] || a[..] == [4, 8, 1, 6, 9] || a[..] == [4, 8, 1, 9, 6] || a[..] == [4, 8, 6, 1, 9] || a[..] == [4, 8, 6, 9, 1] || a[..] == [4, 8, 9, 1, 6] || a[..] == [4, 8, 9, 6, 1] || a[..] == [4, 9, 1, 6, 8] || a[..] == [4, 9, 1, 8, 6] || a[..] == [4, 9, 6, 1, 8] || a[..] == [4, 9, 6, 8, 1] || a[..] == [4, 9, 8, 1, 6] || a[..] == [4, 9, 8, 6, 1] || a[..] == [6, 1, 4, 8, 9] || a[..] == [6, 1, 4, 9, 8] || a[..] == [6, 1, 8, 4, 9] || a[..] == [6, 1, 8, 9, 4] || a[..] == [6, 1, 9, 4, 8] || a[..] == [6, 1, 9, 8, 4] || a[..] == [6, 4, 1, 8, 9] || a[..] == [6, 4, 1, 9, 8] || a[..] == [6, 4, 8, 1, 9] || a[..] == [6, 4, 8, 9, 1] || a[..] == [6, 4, 9, 1, 8] || a[..] == [6, 4, 9, 8, 1] || a[..] == [6, 8, 1, 4, 9] || a[..] == [6, 8, 1, 9, 4] || a[..] == [6, 8, 4, 1, 9] || a[..] == [6, 8, 4, 9, 1] || a[..] == [6, 8, 9, 1, 4] || a[..] == [6, 8, 9, 4, 1] || a[..] == [6, 9, 1, 4, 8] || a[..] == [6, 9, 1, 8, 4] || a[..] == [6, 9, 4, 1, 8] || a[..] == [6, 9, 4, 8, 1] || a[..] == [6, 9, 8, 1, 4] || a[..] == [6, 9, 8, 4, 1] || a[..] == [8, 1, 4, 6, 9] || a[..] == [8, 1, 4, 9, 6] || a[..] == [8, 1, 6, 4, 9] || a[..] == [8, 1, 6, 9, 4] || a[..] == [8, 1, 9, 4, 6] || a[..] == [8, 1, 9, 6, 4] || a[..] == [8, 4, 1, 6, 9] || a[..] == [8, 4, 1, 9, 6] || a[..] == [8, 4, 6, 1, 9] || a[..] == [8, 4, 6, 9, 1] || a[..] == [8, 4, 9, 1, 6] || a[..] == [8, 4, 9, 6, 1] || a[..] == [8, 6, 1, 4, 9] || a[..] == [8, 6, 1, 9, 4] || a[..] == [8, 6, 4, 1, 9] || a[..] == [8, 6, 4, 9, 1] || a[..] == [8, 6, 9, 1, 4] || a[..] == [8, 6, 9, 4, 1] || a[..] == [8, 9, 1, 4, 6] || a[..] == [8, 9, 1, 6, 4] || a[..] == [8, 9, 4, 1, 6] || a[..] == [8, 9, 4, 6, 1] || a[..] == [8, 9, 6, 1, 4] || a[..] == [8, 9, 6, 4, 1] || a[..] == [9, 1, 4, 6, 8] || a[..] == [9, 1, 4, 8, 6] || a[..] == [9, 1, 6, 4, 8] || a[..] == [9, 1, 6, 8, 4] || a[..] == [9, 1, 8, 4, 6] || a[..] == [9, 1, 8, 6, 4] || a[..] == [9, 4, 1, 6, 8] || a[..] == [9, 4, 1, 8, 6] || a[..] == [9, 4, 6, 1, 8] || a[..] == [9, 4, 6, 8, 1] || a[..] == [9, 4, 8, 1, 6] || a[..] == [9, 4, 8, 6, 1] || a[..] == [9, 6, 1, 4, 8] || a[..] == [9, 6, 1, 8, 4] || a[..] == [9, 6, 4, 1, 8] || a[..] == [9, 6, 4, 8, 1] || a[..] == [9, 6, 8, 1, 4] || a[..] == [9, 6, 8, 4, 1] || a[..] == [9, 8, 1, 4, 6] || a[..] == [9, 8, 1, 6, 4] || a[..] == [9, 8, 4, 1, 6] || a[..] == [9, 8, 4, 6, 1] || a[..] == [9, 8, 6, 1, 4] || a[..] == [9, 8, 6, 4, 1];
  // Now we know a[..] is one of these permutations
  // But we also know it's sorted
  // Check which of these are sorted
  assert !sorted([1, 4, 6, 9, 8]);
  assert !sorted([1, 4, 8, 6, 9]);
  assert !sorted([1, 4, 8, 9, 6]);
  assert !sorted([1, 4, 9, 6, 8]);
  assert !sorted([1, 4, 9, 8, 6]);
  assert !sorted([1, 6, 4, 8, 9]);
  assert !sorted([1, 6, 4, 9, 8]);
  assert !sorted([1, 6, 8, 4, 9]);
  assert !sorted([1, 6, 8, 9, 4]);
  assert !sorted([1, 6, 9, 4, 8]);
  assert !sorted([1, 6, 9, 8, 4]);
  assert !sorted([1, 8, 4, 6, 9]);
  assert !sorted([1, 8, 4, 9, 6]);
  assert !sorted([1, 8, 6, 4, 9]);
  assert !sorted([1, 8, 6, 9, 4]);
  assert !sorted([1, 8, 9, 4, 6]);
  assert !sorted([1, 8, 9, 6, 4]);
  assert !sorted([1, 9, 4, 6, 8]);
  assert !sorted([1, 9, 4, 8, 6]);
  assert !sorted([1, 9, 6, 4, 8]);
  assert !sorted([1, 9, 6, 8, 4]);
  assert !sorted([1, 9, 8, 4, 6]);
  assert !sorted([1, 9, 8, 6, 4]);
  assert !sorted([4, 1, 6, 8, 9]);
  assert !sorted([4, 1, 6, 9, 8]);
  assert !sorted([4, 1, 8, 6, 9]);
  assert !sorted([4, 1, 8, 9, 6]);
  assert !sorted([4, 1, 9, 6, 8]);
  assert !sorted([4, 1, 9, 8, 6]);
  assert !sorted([4, 6, 1, 8, 9]);
  assert !sorted([4, 6, 1, 9, 8]);
  assert !sorted([4, 6, 8, 1, 9]);
  assert !sorted([4, 6, 8, 9, 1]);
  assert !sorted([4, 6, 9, 1, 8]);
  assert !sorted([4, 6, 9, 8, 1]);
  assert !sorted([4, 8, 1, 6, 9]);
  assert !sorted([4, 8, 1, 9, 6]);
  assert !sorted([4, 8, 6, 1, 9]);
  assert !sorted([4, 8, 6, 9, 1]);
  assert !sorted([4, 8, 9, 1, 6]);
  assert !sorted([4, 8, 9, 6, 1]);
  assert !sorted([4, 9, 1, 6, 8]);
  assert !sorted([4, 9, 1, 8, 6]);
  assert !sorted([4, 9, 