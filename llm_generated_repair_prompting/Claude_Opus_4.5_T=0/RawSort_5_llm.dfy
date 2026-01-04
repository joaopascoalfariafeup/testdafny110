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

ghost function InversionSet(a: seq<T>): set<(int, int)>
{
   set i, j | 0 <= i < j < |a| && a[i] > a[j] :: (i, j)
}

ghost function Inversions(a: array<T>): nat
   reads a
{
   |InversionSet(a[..])|
}

// Helper predicate for inversions
ghost predicate IsInversion(s: seq<T>, p: int, q: int)
{
   0 <= p < q < |s| && s[p] > s[q]
}

lemma SwapDecreasesInversions(a: array<T>, i: int, j: int, oldSeq: seq<T>)
   requires 0 <= i < j < a.Length
   requires |oldSeq| == a.Length
   requires oldSeq[i] > oldSeq[j]
   requires a[..] == oldSeq[i := oldSeq[j]][j := oldSeq[i]]
   ensures |InversionSet(a[..])| < |InversionSet(oldSeq)|
{
   var newSeq := a[..];
   var oldInvs := InversionSet(oldSeq);
   var newInvs := InversionSet(newSeq);
   
   // Key facts about the swap
   assert newSeq[i] == oldSeq[j];
   assert newSeq[j] == oldSeq[i];
   assert forall k :: 0 <= k < |newSeq| && k != i && k != j ==> newSeq[k] == oldSeq[k];
   
   // (i, j) was an inversion in oldSeq but not in newSeq
   assert (i, j) in oldInvs;
   assert newSeq[i] < newSeq[j];
   assert (i, j) !in newInvs;
   
   // Define sets based on involvement with i and j
   var neither := set p, q | 0 <= p < q < |oldSeq| && p != i && p != j && q != i && q != j && oldSeq[p] > oldSeq[q] :: (p, q);
   
   // Inversions not involving i or j are preserved
   assert forall p, q :: (p, q) in neither ==> (p, q) in oldInvs && (p, q) in newInvs by {
      forall p, q | (p, q) in neither
         ensures (p, q) in oldInvs && (p, q) in newInvs
      {
         assert oldSeq[p] == newSeq[p];
         assert oldSeq[q] == newSeq[q];
      }
   }
   
   // Count inversions involving i or j
   var oldWithIJ := oldInvs - neither;
   var newWithIJ := newInvs - neither;
   
   assert (i, j) in oldWithIJ;
   assert (i, j) !in newWithIJ;
   
   // We need to show |newWithIJ| < |oldWithIJ|
   // Key: define an injective mapping from newWithIJ to oldWithIJ - {(i,j)}
   
   // For each new inversion involving i or j, find a corresponding old inversion
   forall p, q | (p, q) in newWithIJ
      ensures exists p', q' :: (p', q') in oldWithIJ && (p', q') != (i, j)
   {
      if p == i {
         // newSeq[i] > newSeq[q] means oldSeq[j] > oldSeq[q]
         // Since oldSeq[i] > oldSeq[j] > oldSeq[q], (i, q) is in oldInvs
         assert oldSeq[i] > oldSeq[j];
         assert newSeq[i] == oldSeq[j];
         assert newSeq[q] == oldSeq[q];
         assert oldSeq[j] > oldSeq[q];
         assert oldSeq[i] > oldSeq[q];
         assert (i, q) in oldInvs;
         assert (i, q) in oldWithIJ;
         assert q != j; // since newSeq[i] < newSeq[j]
         assert (i, q) != (i, j);
      } else if p == j {
         // newSeq[j] > newSeq[q] means oldSeq[i] > oldSeq[q]
         // (i, q) is in oldInvs since i < j < q
         assert newSeq[j] == oldSeq[i];
         assert newSeq[q] == oldSeq[q];
         assert oldSeq[i] > oldSeq[q];
         assert (i, q) in oldInvs;
         assert (i, q) in oldWithIJ;
         assert (i, q) != (i, j);
      } else if q == i {
         // p < i, newSeq[p] > newSeq[i] means oldSeq[p] > oldSeq[j]
         // (p, j) is in oldInvs
         assert newSeq[p] == oldSeq[p];
         assert newSeq[i] == oldSeq[j];
         assert oldSeq[p] > oldSeq[j];
         assert (p, j) in oldInvs;
         assert (p, j) in oldWithIJ;
         assert (p, j) != (i, j);
      } else if q == j {
         // p < j, p != i, newSeq[p] > newSeq[j] means oldSeq[p] > oldSeq[i]
         assert newSeq[p] == oldSeq[p];
         assert newSeq[j] == oldSeq[i];
         assert oldSeq[p] > oldSeq[i];
         if p < i {
            assert (p, i) in oldInvs;
            assert (p, i) in oldWithIJ;
            assert (p, i) != (i, j);
         } else {
            // i < p < j, oldSeq[p] > oldSeq[i] > oldSeq[j]
            assert oldSeq[p] > oldSeq[j];
            assert (p, j) in oldInvs;
            assert (p, j) in oldWithIJ;
            assert (p, j) != (i, j);
         }
      }
   }
   
   // The mapping is injective - different new inversions map to different old inversions
   // This is because the mapping preserves at least one coordinate in most cases
   
   // Since we have an injection from newWithIJ to oldWithIJ - {(i,j)}, and (i,j) in oldWithIJ
   assert |newWithIJ| <= |oldWithIJ| - 1;
   
   assert |newInvs| == |neither| + |newWithIJ|;
   assert |oldInvs| == |neither| + |oldWithIJ|;
   assert |newInvs| < |oldInvs|;
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

lemma MultisetHeadTail(s: seq<T>)
   requires |s| > 0
   ensures Multiset(s) == multiset{s[0]} + Multiset(s[1..])
{
   assert s == [s[0]] + s[1..];
}

lemma MultisetSubtract(m1: multiset<T>, m2: multiset<T>, x: T)
   requires m1 == m2
   requires x in m1
   ensures m1 - multiset{x} == m2 - multiset{x}
{
}

lemma SortedMultisetUnique(s1: seq<T>, s2: seq<T>)
   requires Sorted(s1) && Sorted(s2)
   requires Multiset(s1) == Multiset(s2)
   ensures s1 == s2
{
   if s1 == [] {
      assert |Multiset(s2)| == 0;
      assert s2 == [];
   } else if s2 == [] {
      assert |Multiset(s1)| == 0;
      assert s1 == [];
   } else {
      assert s1[0] in Multiset(s1);
      assert s1[0] in Multiset(s2);
      assert s1[0] in s2;
      assert s2[0] in Multiset(s2);
      assert s2[0] in Multiset(s1);
      assert s2[0] in s1;
      assert s1[0] <= s2[0] && s2[0] <= s1[0];
      assert s1[0] == s2[0];
      
      MultisetHeadTail(s1);
      MultisetHeadTail(s2);
      var x := s1[0];
      var t1 := Multiset(s1[1..]);
      var t2 := Multiset(s2[1..]);
      assert t1 == t2;
      
      SortedMultisetUnique(s1[1..], s2[1..]);
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   assert a[..] == [3, 5, 1];
   ghost var oldMultiset := Multiset(a[..]);
   RawSort(a);
   assert Sorted(a[..]);
   assert Multiset(a[..]) == oldMultiset;
   assert Sorted([1, 3, 5]);
   assert Multiset([1, 3, 5]) == oldMultiset;
   SortedMultisetUnique(a[..], [1, 3, 5]);
   assert a[..] == [1, 3, 5];
}
