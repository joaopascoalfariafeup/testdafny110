/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helpful lemma: any suffix of a sorted sequence is sorted.
lemma SortedSuffix(s: seq<int>, k: int)
  requires Sorted(s)
  requires 0 <= k <= |s|
  ensures Sorted(s[k..])
{
  // Directly use Sorted(s) with shifted indices
  assert forall i, j :: 0 <= i < j < |s[k..]| ==> s[k..][i] <= s[k..][j] by {
    // relate suffix indexing to original sequence indexing
    assert s[k..][i] == s[k + i];
    assert s[k..][j] == s[k + j];
    assert 0 <= k + i;
    assert k + i < k + j;
    assert k + j < |s|;
  }
}

// Insert x into an already-sorted sequence s, preserving sortedness and multiset.
ghost function {:fuel 50} insertSorted(x: int, s: seq<int>): seq<int>
  requires Sorted(s)
  ensures Sorted(insertSorted(x, s))
  ensures multiset(insertSorted(x, s)) == multiset(s) + multiset([x])
  ensures |insertSorted(x, s)| == |s| + 1
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else
    (SortedSuffix(s, 1);
     var t := insertSorted(x, s[1..]);
     // Establish s[0] <= every element of t, then [s[0]]+t is sorted.
     assert Sorted(t); // from recursion
     assert forall u :: 0 <= u < |s[1..]| ==> s[0] <= s[1..][u]; // from Sorted(s)

     assert forall u :: 0 <= u < |t| ==> s[0] <= t[u] by {
       // Since x > s[0] and every element of s[1..] is >= s[0], and t is a permutation of s[1..] plus x,
       // every element of t is >= s[0].
       assert x > s[0]; // from else-branch condition
       assert forall v :: 0 <= v < |s[1..]| ==> s[0] <= s[1..][v];
     }

     // With s[0] <= all of t and Sorted(t), concatenation is sorted.
     assert Sorted([s[0]] + t) by {
       assert forall i, j :: 0 <= i < j < |[s[0]] + t| ==> ([s[0]] + t)[i] <= ([s[0]] + t)[j] by {
         if i == 0 {
           assert j >= 1;
           assert ([s[0]] + t)[0] == s[0];
           assert ([s[0]] + t)[j] == t[j-1];
           assert s[0] <= t[j-1];
         } else {
           assert ([s[0]] + t)[i] == t[i-1];
           assert ([s[0]] + t)[j] == t[j-1];
           assert 0 <= i-1 < j-1 < |t|;
           assert t[i-1] <= t[j-1];
         }
       }
     }
     [s[0]] + t)
}

// A ghost "sorting" function: return the unique sorted permutation of s.
ghost function {:fuel 50} sorted(s: seq<int>): seq<int>
  ensures Sorted(sorted(s))
  ensures multiset(sorted(s)) == multiset(s)
  decreases |s|
{
  if |s| <= 1 then s
  else
    insertSorted(s[0], sorted(s[1..]))
}

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    for i := 0 to a.Length 
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant forall x, y :: 0 <= x < i <= y < a.Length ==> a[x] <= a[y]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i <= j <= a.Length
          invariant i <= jMin < a.Length
          invariant forall k :: i <= k < j ==> a[jMin] <= a[k]
        {
            if a[j] < a[jMin] {
                jMin := j;
            }
        } 
        if jMin != i {
          a[i], a[jMin] := a[jMin], a[i]; 
        }

        assert forall y :: i <= y < a.Length ==> a[i] <= a[y];
        assert Sorted(a[..i+1]);
    }
}


// Test case checked statically.
method testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  assert a[..] == [9, 4, 6, 1, 8];

  SelectionSort(a);

  assert a.Length == 5;
  assert a[..] == a[..a.Length];

  assert Sorted(a[..]);
  assert multiset(a[..]) == multiset([9, 4, 6, 1, 8]);
  assert a[..] == [1, 4, 6, 8, 9];
}
