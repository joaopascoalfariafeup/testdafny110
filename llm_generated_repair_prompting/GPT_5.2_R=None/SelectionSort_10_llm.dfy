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
  // straightforward: Sorted(s[k..]) is exactly Sorted(s) restricted to indices >= k
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
     [s[0]] + t)
}

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
          invariant i + 1 <= j <= a.Length  // because j starts at i+1
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
