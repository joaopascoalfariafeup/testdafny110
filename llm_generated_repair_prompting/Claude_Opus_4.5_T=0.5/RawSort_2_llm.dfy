/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

ghost predicate Sorted(s: seq<T>)
{
   forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function Multiset(s: seq<T>): multiset<T>
{
   multiset(s)
}

ghost function Inversions(a: array<T>): nat
   reads a
{
   |set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j)|
}

ghost function InversionSet(a: array<T>): set<(int, int)>
   reads a
{
   set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j)
}

lemma SwapDecreasesInversions(a: array<T>, i: int, j: int, oldSeq: seq<T>)
   requires 0 <= i < j < a.Length
   requires |oldSeq| == a.Length
   requires oldSeq[i] > oldSeq[j]
   requires a[..] == oldSeq[i := oldSeq[j]][j := oldSeq[i]]
   ensures Inversions(a) < |set p, q | 0 <= p < q < |oldSeq| && oldSeq[p] > oldSeq[q] :: (p, q)|
{
   var oldInvSet := set p, q | 0 <= p < q < |oldSeq| && oldSeq[p] > oldSeq[q] :: (p, q);
   var newInvSet := InversionSet(a);
   
   // The pair (i, j) was an inversion in old but not in new
   assert (i, j) in oldInvSet;
   assert (i, j) !in newInvSet;
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a[..])
   ensures Multiset(a[..]) == Multiset(old(a[..]))
   decreases Inversions(a)
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var oldInv := Inversions(a);
      ghost var oldMultiset := Multiset(a[..]);
      ghost var oldSeq := a[..];
      a[i], a[j] := a[j], a[i]; // swap
      assert Multiset(a[..]) == oldMultiset;
      SwapDecreasesInversions(a, i, j, oldSeq);
      assert Inversions(a) < oldInv;
      RawSort(a); // proceed recursivelly
   }
}

lemma SortedMultisetUnique(s1: seq<T>, s2: seq<T>)
   requires Sorted(s1)
   requires Sorted(s2)
   requires Multiset(s1) == Multiset(s2)
   ensures s1 == s2
{
   if s1 == [] {
      assert |Multiset(s2)| == 0;
   } else if s2 == [] {
      assert |Multiset(s1)| == 0;
   } else {
      assert s1[0] in Multiset(s1);
      assert s2[0] in Multiset(s2);
      assert s1[0] in Multiset(s2);
      assert s2[0] in Multiset(s1);
      // Both are sorted, so s1[0] is min of s1 and s2[0] is min of s2
      // Since they have same multiset, mins must be equal
      assert forall k :: 0 <= k < |s1| ==> s1[0] <= s1[k];
      assert forall k :: 0 <= k < |s2| ==> s2[0] <= s2[k];
      assert s1[0] == s2[0];
      assert Multiset(s1[1..]) == Multiset(s1) - multiset{s1[0]};
      assert Multiset(s2[1..]) == Multiset(s2) - multiset{s2[0]};
      SortedMultisetUnique(s1[1..], s2[1..]);
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   ghost var oldSeq := a[..];
   assert oldSeq == [3, 5, 1];
   RawSort(a);
   assert Sorted(a[..]);
   assert Multiset(a[..]) == Multiset(oldSeq);
   assert Multiset(oldSeq) == multiset{3, 5, 1};
   assert Sorted([1, 3, 5]);
   assert Multiset([1, 3, 5]) == multiset{1, 3, 5};
   assert multiset{3, 5, 1} == multiset{1, 3, 5};
   SortedMultisetUnique(a[..], [1, 3, 5]);
   assert a[..] == [1, 3, 5];
}
